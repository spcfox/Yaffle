module Core.Termination.CallGraph

import Core.Context
import Core.Context.Log
import Core.Env
import Core.TT
import Core.Evaluate

import Data.SnocList

import Libraries.Data.NameMap
import Libraries.Data.NameMap.Traversable

%default covering

-- Drop any non-inf top level laziness annotations
dropLazy : Value f vars -> Core (Glued vars)
dropLazy val@(VDelayed _ r t)
    = case r of
           LInf => pure (asGlued val)
           _ => pure t
dropLazy val@(VDelay _ r t v)
    = case r of
           LInf => pure (asGlued val)
           _ => pure v
dropLazy val@(VForce fc r v sp)
    = case r of
           LInf => pure (asGlued val)
           _ => applyAll fc v (cast (map (\ e => (multiplicity e, value e)) sp))
dropLazy val = pure (asGlued val)

-- Equal for the purposes of size change means, ignoring as patterns, all
-- non-metavariable positions are equal
scEq : NameMap (SnocList (Glued [<])) -> Value f [<] -> Value f' [<] -> Core Bool

scEqSpine : NameMap (SnocList (Glued [<])) -> Spine [<] -> Spine [<] -> Core Bool
scEqSpine _ [<] [<] = pure True
scEqSpine substs (sp :< x) (sp' :< y)
    = do x' <- value x
         y' <- value y
         if !(scEq substs x' y')
            then scEqSpine substs sp sp'
            else pure False
scEqSpine _ _ _ = pure False

-- Approximate equality between values. We don't go under binders - we're
-- only checking for size change equality so expect to just see type and
-- data constructors
-- TODO: size change for pattern matching on types
scEq' : NameMap (SnocList (Glued [<])) -> Value f [<] -> Value f' [<] -> Core Bool
scEq' substs (VApp _ _ n sp _) (VApp _ _ n' sp' _)
    = if n == n'
         then scEqSpine substs sp sp'
         else pure False
-- Should never see this since we always call with vars = [<], but it is
-- technically possible
scEq' substs (VLocal _ idx _ sp) (VLocal _ idx' _ sp')
    = if idx == idx'
         then scEqSpine substs sp sp'
         else pure False
scEq' substs (VDCon _ _ t a sp) (VDCon _ _ t' a' sp')
    = if t == t'
         then scEqSpine substs sp sp'
         else pure False
scEq' substs (VTCon _ n a sp) (VTCon _ n' a' sp')
    = if n == n'
         then scEqSpine substs sp sp'
         else pure False
scEq' substs (VMeta{}) _ = pure True
scEq' substs _ (VMeta{}) = pure True
scEq' substs (VAs _ _ a p) p' = scEq substs p p'
scEq' substs p (VAs _ _ a p') = scEq substs p p'
scEq' substs (VDelayed _ _ t) (VDelayed _ _ t') = scEq substs t t'
scEq' substs (VDelay _ _ t x) (VDelay _ _ t' x')
     = if !(scEq substs t t') then scEq substs x x'
          else pure False
scEq' substs (VForce _ _ t [<]) (VForce _ _ t' [<]) = scEq substs t t'
scEq' substs (VPrimVal _ c) (VPrimVal _ c') = pure $ c == c'
scEq' substs (VErased _ _) (VErased _ _) = pure True
scEq' substs (VUnmatched _ _) (VUnmatched _ _) = pure True
scEq' substs (VType _ _) (VType _ _) = pure True
scEq' _ _ _ = pure False -- other cases not checkable

scEq'' : NameMap (SnocList (Glued [<])) -> Value f [<] -> Value f' [<] -> Core Bool
scEq'' substs s t@(VApp _ Bound nm _ _)
    = do False <- scEq' substs s t
           | True => pure True
         case lookup nm substs of
           Just ts => anyM (scEq substs s) $ toList ts
           Nothing => pure False
scEq'' substs s t = scEq' substs s t

scEq substs x y = scEq'' substs !(dropLazy x) !(dropLazy y)

data Guardedness = Toplevel | Unguarded | Guarded | InDelay

Show Guardedness where
  show Toplevel = "Toplevel"
  show Unguarded = "Unguarded"
  show Guarded = "Guarded"
  show InDelay = "InDelay"

assertedSmaller : NameMap (SnocList (Glued [<])) -> Maybe (Glued [<]) ->
                  Glued [<] -> Core Bool
assertedSmaller substs (Just b) a = scEq substs b a
assertedSmaller _ _ _ = pure False

-- Return whether first argument is structurally smaller than the second.
smaller : Bool -> -- Have we gone under a constructor yet?
          Maybe (Glued [<]) -> -- Asserted bigger thing
          NameMap (SnocList (Glued [<])) -> -- Substitutions
          Glued [<] -> -- Term we're checking
          Glued [<] -> -- Argument it might be smaller than
          Core Bool

smallerArg : Bool ->
             Maybe (Glued [<]) -> NameMap (SnocList (Glued [<])) ->
             Glued [<] -> Glued [<] -> Core Bool
smallerArg inc big substs (VAs _ _ _ s) tm = smallerArg inc big substs s tm
smallerArg inc big substs s tm
      -- If we hit a pattern that is equal to a thing we've asserted_smaller,
      -- the argument must be smaller
    = if !(assertedSmaller substs big tm)
         then pure True
         else case tm of
                   VDCon _ _ _ _ sp
                       => anyM (smaller True big substs s)
                                (cast !(traverseSnocList value sp))
                   _ => case s of
                             VApp fc nt n sp@(_ :< _) _ =>
                                -- Higher order recursive argument
                                  smaller inc big substs
                                      (VApp fc nt n [<] (pure Nothing))
                                      tm
                             _ => pure False

smaller' : Bool ->
           Maybe (Glued [<]) -> NameMap (SnocList (Glued [<])) ->
           Glued [<] -> Glued [<] -> Core Bool
smaller' inc big substs _ (VErased _ _) = pure False -- Never smaller than an erased thing!
-- for an as pattern, it's smaller if it's smaller than the pattern
-- or if we've gone under a constructor and it's smaller than the variable
smaller' True big substs s (VAs _ _ a t)
    = if !(smaller' True big substs s a)
         then pure True
         else smaller' True big substs s t
smaller' True big substs s t
    = if !(scEq substs s t)
         then pure True
         else smallerArg True big substs s t
smaller' inc big substs s t = smallerArg inc big substs s t

smaller inc big substs s t@(VApp _ Bound nm _ _)
    = do False <- smaller' inc big substs s t
           | True => pure True
         case lookup nm substs of
           Just ts => anyM (smaller inc big substs s) $ toList ts
           Nothing => pure False
smaller inc big substs s t = smaller' inc big substs s t

data SCVar : Type where

mkvar : Int -> Value f [<]
mkvar i = VApp EmptyFC Bound (MN "scv" i) [<] (pure Nothing)

nextVar : {auto c : Ref SCVar Int} -> Core (Value f [<])
nextVar
    = do v <- get SCVar
         put SCVar (v + 1)
         pure (mkvar v)

ForcedEqs : Type
ForcedEqs = List (Glued [<], Glued [<])

findSC : {auto c : Ref Ctxt Defs} ->
         {auto v : Ref SCVar Int} ->
         Guardedness ->
         ForcedEqs ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         NameMap (SnocList (Glued [<])) -> -- Substitutions
         Glued [<] -> -- definition. No expanding to NF, we want to check
                      -- the program as written (plus tcinlines)
         Core (List SCCall)

-- Expand the size change argument list with 'Nothing' to match the given
-- arity (i.e. the arity of the function we're calling) to ensure that
-- it's noted that we don't know the size change relationship with the
-- extra arguments.
expandToArity : Nat -> List (Maybe (Nat, SizeChange)) ->
                List (Maybe (Nat, SizeChange))
expandToArity Z xs = xs
expandToArity (S k) (x :: xs) = x :: expandToArity k xs
expandToArity (S k) [] = Nothing :: expandToArity k []

findVar : Int -> List (Glued vars, Glued vars) -> Maybe (Glued vars)
findVar i [] = Nothing
findVar i ((VApp _ Bound (MN _ i') _ _, tm) :: eqs)
    = if i == i' then Just tm else findVar i eqs
findVar i (_ :: eqs) = findVar i eqs

canonicalise : List (Glued vars, Glued vars) -> Glued vars -> Core (Glued vars)
canonicalise eqs tm@(VApp _ Bound (MN _ i) _ _)
    = case findVar i eqs of
           Nothing => pure tm
           Just val => canonicalise eqs val
canonicalise eqs (VDCon fc cn t a sp)
    = pure $ VDCon fc cn t a !(canonSp sp)
  where
    canonSp : Spine vars -> Core (Spine vars)
    canonSp [<] = pure [<]
    canonSp (rest :< MkSpineEntry fc c arg)
        = do rest' <- canonSp rest
             pure (rest' :< MkSpineEntry fc c (canonicalise eqs !arg))
-- for matching on types, convert to the form the case tree builder uses
canonicalise eqs (VPrimVal fc (PrT c))
    = pure $ (VTCon fc (UN (Basic $ show c)) 0 [<])
canonicalise eqs (VType fc _)
    = pure $ (VTCon fc (UN (Basic "Type")) 0 [<])
canonicalise eqs val = pure val

-- if the argument is an 'assert_smaller', return the thing it's smaller than
asserted : ForcedEqs -> Name -> Glued [<] -> Core (Maybe (Glued [<]))
asserted eqs aSmaller (VApp _ nt fn [<_, _, e, _] _)
     = if fn == aSmaller
          then Just <$> canonicalise eqs !(value e)
          else pure Nothing
asserted _ _ _ = pure Nothing

-- Calculate the size change for the given argument.
-- i.e., return the size relationship of the given argument with an entry
-- in 'pats'; the position in 'pats' and the size change.
-- Nothing if there is no relation with any of them.
mkChange : {auto c : Ref Ctxt Defs} ->
           ForcedEqs ->
           Name ->
           NameMap (SnocList (Glued [<])) ->
           (pats : List (Nat, Glued [<])) ->
           (arg : Glued [<]) ->
           Core (Maybe (Nat, SizeChange))
mkChange eqs aSmaller substs [] arg = pure Nothing
mkChange eqs aSmaller substs ((i, parg) :: pats) arg
    = if !(scEq substs arg parg)
         then pure (Just (i, Same))
         else do s <- smaller False !(asserted eqs aSmaller arg) substs arg parg
                 if s then pure (Just (i, Smaller))
                      else mkChange eqs aSmaller substs pats arg

findSCcall : {auto c : Ref Ctxt Defs} ->
             {auto v : Ref SCVar Int} ->
             Guardedness ->
             ForcedEqs ->
             List (Nat, Glued [<]) ->
             NameMap (SnocList (Glued [<])) ->
             FC -> Name -> Nat -> List (Glued [<]) ->
             Core (List SCCall)
findSCcall g eqs pats substs fc fn_in arity args
        -- Under 'assert_total' we assume that all calls are fine, so leave
        -- the size change list empty
      = do args <- traverse (canonicalise eqs) args
           substs <- traverseNameMap (const $ traverseSnocList $ canonicalise eqs) substs

           defs <- get Ctxt
           fn <- getFullName fn_in
           logC "totality.termination.sizechange" 10 $ do pure "Looking under \{show fn}"
           aSmaller <- resolved (gamma defs) (NS builtinNS (UN $ Basic "assert_smaller"))
           logC "totality.termination.sizechange" 10 $
               do under <- traverse (\ (n, t) =>
                              pure (n, !(toFullNames !(quoteNF [<] t)))) pats
                  targs <- traverse (\t => toFullNames !(quoteNF [<] t)) args
                  pure ("Under " ++ show under ++ "\n" ++ "Args " ++ show targs)

           if fn == NS builtinNS (UN $ Basic "assert_total")
              then pure []
              else
               do scs <- traverse (findSC g eqs pats substs) args
                  pure ([MkSCCall fn
                           (expandToArity arity
                                !(traverse (mkChange eqs aSmaller substs pats) args))
                           fc]
                           ++ concat scs)

addSubstitution : Name -> Glued [<] ->
                NameMap (SnocList (Glued [<])) -> NameMap (SnocList (Glued [<]))
addSubstitution nm val = merge $ fromList [(nm, [< val])]

findSCscope : {auto c : Ref Ctxt Defs} ->
              {auto v : Ref SCVar Int} ->
         Guardedness ->
         ForcedEqs ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         NameMap (SnocList (Glued [<])) -> -- Substitutions
         Maybe Name -> -- variable we're splitting on (if it is a variable)
         FC -> Glued [<] ->
         (args : _) -> VCaseScope args [<] -> -- case alternative
         Core (List SCCall)
findSCscope g eqs args substs var fc pat [<] sc
   = do (eqsc, rhs) <- sc
        logC "totality.termination.sizechange" 10 $
            (do tms <- traverse (\ (gx, gy) =>
                            pure (!(toFullNames !(quote [<] gx)),
                                  !(toFullNames !(quote [<] gy)))) eqsc
                pure ("Force equalities " ++ show tms))
        let eqs' = eqsc ++ eqs
        let substs' = maybe substs (\v => addSubstitution v pat substs) var
        logNF "totality.termination.sizechange" 10 "RHS" [<] rhs
        findSC g eqs'
               !(traverse (\ (n, arg) => pure (n, !(canonicalise eqs' arg))) args)
               substs'
               rhs
findSCscope g eqs args substs var fc pat (cargs :< (c, xn)) sc
   = do varg <- nextVar
        pat' <- the (Core (Glued [<])) $ case pat of
                  VDCon vfc n t a sp =>
                      pure (VDCon vfc n t a (sp :< MkSpineEntry fc c (pure varg)))
                  _ => throw (InternalError "Not a data constructor in findSCscope")
        findSCscope g eqs args substs var fc pat' cargs (sc (pure varg))

findSCalt : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
         Guardedness ->
         ForcedEqs ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         NameMap (SnocList (Glued [<])) ->
         Maybe Name -> -- variable we're splitting on (if it is a variable)
         VCaseAlt [<] -> -- case alternative
         Core (List SCCall)
findSCalt g eqs args substs var (VConCase fc n t cargs sc)
    = findSCscope g eqs args substs var fc (VDCon fc n t (length cargs) [<]) _ sc
findSCalt g eqs args substs var (VDelayCase fc ty arg tm)
    = do targ <- nextVar
         varg <- nextVar
         (eqs, rhs) <- tm (pure targ) (pure varg)
         let pat = VDelay fc LUnknown targ varg
         let substs' = maybe substs (\v => addSubstitution v pat substs) var
         findSC g eqs args substs rhs
findSCalt g eqs args substs var (VConstCase fc c tm)
    = do let pat = VPrimVal fc c
         let substs' = maybe substs (\v => addSubstitution v pat substs) var
         findSC g eqs args substs tm
findSCalt g eqs args substs var (VDefaultCase fc tm) = findSC g eqs args substs tm

findSCspine : {auto c : Ref Ctxt Defs} ->
         {auto v : Ref SCVar Int} ->
         Guardedness ->
         ForcedEqs ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         NameMap (SnocList (Glued [<])) ->
         Spine [<] ->
         Core (List SCCall)
findSCspine g eqs pats substs [<] = pure []
findSCspine g eqs pats substs (sp :< e)
    = do vCalls <- findSC g eqs pats substs !(value e)
         spCalls <- findSCspine g eqs pats substs sp
         pure (vCalls ++ spCalls)

findSCapp : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
         Guardedness ->
         ForcedEqs ->
         List (Nat, Glued [<]) -> -- LHS args and their position
         NameMap (SnocList (Glued [<])) ->
         Glued [<] -> -- dealing with cases where this is an application
                      -- of some sort
         Core (List SCCall)
findSCapp g eqs pats substs (VLocal fc _ _ sp)
    = do args <- traverseSnocList value sp
         scs <- traverseSnocList (findSC g eqs pats substs) args
         pure (concat scs)
findSCapp g eqs pats substs (VApp fc Bound _ sp _)
    = do args <- traverseSnocList value sp
         scs <- traverseSnocList (findSC g eqs pats substs) args
         pure (concat scs)
findSCapp g eqs pats substs (VApp fc Func fn sp _)
    = do defs <- get Ctxt
         args <- traverseSnocList value sp
         Just ty <- lookupTyExact fn (gamma defs)
            | Nothing => do
                log "totality" 50 $ "Lookup failed"
                findSCcall Unguarded eqs pats substs fc fn 0 (cast args)
         allg <- allGuarded fn
         -- If it has the all guarded flag, pretend it's a data constructor
         -- Otherwise just carry on as normal
         if allg
            then findSCapp g eqs pats substs (VDCon fc fn 0 0 sp)
            else case g of
                    -- constructor guarded and delayed, so just check the
                    -- arguments
                    InDelay => findSCspine Unguarded eqs pats substs sp
                    _ => do arity <- getArity [<] ty
                            findSCcall Unguarded eqs pats substs fc fn arity (cast args)
  where
    allGuarded : Name -> Core Bool
    allGuarded n
        = do defs <- get Ctxt
             Just gdef <- lookupCtxtExact n (gamma defs)
                  | Nothing => pure False
             pure (AllGuarded `elem` flags gdef)
findSCapp InDelay eqs pats substs (VDCon fc n t a sp)
    = findSCspine InDelay eqs pats substs sp
findSCapp Guarded eqs pats substs (VDCon fc n t a sp)
    = do defs <- get Ctxt
         Just ty <- lookupTyExact n (gamma defs)
              | Nothing => do
                   log "totality" 50 $ "Lookup failed"
                   findSCcall Guarded eqs pats substs fc n 0 (cast !(traverseSnocList value sp))
         arity <- getArity [<] ty
         findSCcall Guarded eqs pats substs fc n arity (cast !(traverseSnocList value sp))
findSCapp Toplevel eqs pats substs (VDCon fc n t a sp)
    = do defs <- get Ctxt
         Just ty <- lookupTyExact n (gamma defs)
              | Nothing => do
                   log "totality" 50 $ "Lookup failed"
                   findSCcall Guarded eqs pats substs fc n 0 (cast !(traverseSnocList value sp))
         arity <- getArity [<] ty
         findSCcall Guarded eqs pats substs fc n arity (cast !(traverseSnocList value sp))
findSCapp g eqs pats substs tm = pure [] -- not an application (TODO: VTCon)

-- If we're Guarded and find a Delay, continue with the argument as InDelay
findSC Guarded eqs pats substs (VDelay _ LInf _ tm)
    = findSC InDelay eqs pats substs tm
findSC g eqs args substs (VLam fc x c p ty sc)
    = do v <- nextVar
         findSC g eqs args substs !(sc v)
findSC g eqs args substs (VBind fc n b sc)
    = do v <- nextVar
         pure $ !(findSCbinder b) ++ !(findSC g eqs args substs !(sc (pure v)))
  where
      findSCbinder : Binder (Glued [<]) -> Core (List SCCall)
      findSCbinder (Let _ c val ty) = findSC Unguarded eqs args substs val
      findSCbinder _ = pure []
findSC g eqs pats substs (VDelay _ _ _ tm)
    = findSC g eqs pats substs tm
findSC g eqs pats substs (VForce _ _ v sp)
    = do vCalls <- findSC g eqs pats substs v
         spCalls <- findSCspine Unguarded eqs pats substs sp
         pure (vCalls ++ spCalls)
findSC g eqs args substs (VCase fc ct c (VApp _ Bound n [<] _) scTy alts)
    = do altCalls <- traverse (findSCalt g eqs args substs (Just n)) alts
         pure (concat altCalls)
findSC g eqs args substs (VCase fc ct c sc scTy alts)
    = do altCalls <- traverse (findSCalt g eqs args substs Nothing) alts
         scCalls <- findSC Unguarded eqs args substs (asGlued sc)
         pure (scCalls ++ concat altCalls)
findSC g eqs pats substs tm = findSCapp g eqs pats substs tm

findSCTop : {auto c : Ref Ctxt Defs} ->
            {auto v : Ref SCVar Int} ->
            Nat -> List (Nat, Glued [<]) -> Glued [<] -> Core (List SCCall)
findSCTop i args (VLam fc x c p ty sc)
    = do arg <- nextVar
         findSCTop (i + 1) ((i, arg) :: args) !(sc arg)
findSCTop i args def = findSC Toplevel [] (reverse args) empty def

getSC : {auto c : Ref Ctxt Defs} ->
        Defs -> Def -> Core (List SCCall)
getSC defs (Function _ tm _ _)
   = do ntm <- nfTotality [<] tm
        logNF "totality.termination.sizechange" 5 "From tree" [<] ntm
        v <- newRef SCVar 0
        sc <- findSCTop 0 [] ntm
        pure $ nub sc
getSC defs _ = pure []

export
calculateSizeChange : {auto c : Ref Ctxt Defs} ->
                      FC -> Name -> Core (List SCCall)
calculateSizeChange loc n
    = do logC "totality.termination.sizechange" 5 $ do pure "Calculating Size Change: \{show !(toFullNames n)}"
         defs <- get Ctxt
         Just def <- lookupCtxtExact n (gamma defs)
              | Nothing => undefinedName loc n
         r <- getSC defs (definition def)
         log "totality.termination.sizechange" 5 $ "Calculated: " ++ show r
         pure r
