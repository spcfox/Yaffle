module TTImp.ProcessFnOpt

import Core.Context
import Core.Context.Log
import Core.Evaluate

import TTImp.TTImp

import Data.SnocList
import Libraries.Data.NameMap

getRetTy : {auto c : Ref Ctxt Defs} ->
           NF [<] -> Core Name
getRetTy (VBind fc _ (Pi _ _ _ _) sc)
    = getRetTy !(expand !(sc (pure (VErased fc Placeholder))))
getRetTy (VTCon _ n _ _) = pure n
getRetTy ty
    = throw (GenericMsg (getLoc ty)
             "Can only add hints for concrete return types")

throwIfHasFlag : {auto c : Ref Ctxt Defs} -> FC -> Name -> DefFlag -> String -> Core ()
throwIfHasFlag fc ndef fl msg
    = when !(hasFlag fc ndef fl) $ throw (GenericMsg fc msg)

export
processFnOpt : {auto c : Ref Ctxt Defs} ->
               FC -> Bool -> -- ^ top level name?
               Name -> FnOpt -> Core ()
processFnOpt fc _ ndef Unsafe
    = pure () -- TODO: Not implemented
processFnOpt fc _ ndef Inline
    = do throwIfHasFlag fc ndef NoInline "%noinline and %inline are mutually exclusive"
         setFlag fc ndef Inline
processFnOpt fc _ ndef NoInline
    = do throwIfHasFlag fc ndef Inline "%inline and %noinline are mutually exclusive"
         setFlag fc ndef NoInline
processFnOpt fc _ ndef Deprecate
    =  setFlag fc ndef Deprecate
processFnOpt fc _ ndef TCInline
    = setFlag fc ndef TCInline
processFnOpt fc True ndef (Hint d)
    = do defs <- get Ctxt
         Just ty <- lookupTyExact ndef (gamma defs)
              | Nothing => undefinedName fc ndef
         target <- getRetTy !(expand !(nf [<] ty))
         addHintFor fc target ndef d False
processFnOpt fc _ ndef (Hint d)
    = do log "elab" 5 $ "Adding local hint " ++ show !(toFullNames ndef)
         addLocalHint ndef
processFnOpt fc True ndef (GlobalHint a)
    = addGlobalHint ndef a
processFnOpt fc _ ndef (GlobalHint a)
    = throw (GenericMsg fc "%globalhint is not valid in local definitions")
processFnOpt fc _ ndef ExternFn
    = setFlag fc ndef Inline -- if externally defined, inline when compiling
processFnOpt fc _ ndef (ForeignFn _)
    = setFlag fc ndef Inline -- if externally defined, inline when compiling
processFnOpt fc _ ndef (ForeignExport _)
    = pure ()
processFnOpt fc _ ndef Invertible
    = setFlag fc ndef Invertible
processFnOpt fc _ ndef (Totality tot)
    = setFlag fc ndef (SetTotal tot)
processFnOpt fc _ ndef Macro
    = setFlag fc ndef Macro
processFnOpt fc _ ndef (SpecArgs ns)
    = do defs <- get Ctxt
         Just gdef <- lookupCtxtExact ndef (gamma defs)
              | Nothing => undefinedName fc ndef
         nty <- expand !(nf [<] (type gdef))
         ps <- getNamePos 0 nty
         ddeps <- collectDDeps nty
         specs <- collectSpec [] ddeps ps nty
         ignore $ addDef ndef ({ specArgs := specs } gdef)
  where
    insertDeps : List Nat -> List (Name, Nat) -> List Name -> List Nat
    insertDeps acc ps [] = acc
    insertDeps acc ps (n :: ns)
        = case lookup n ps of
               Nothing => insertDeps acc ps ns
               Just pos => if pos `elem` acc
                              then insertDeps acc ps ns
                              else insertDeps (pos :: acc) ps ns

    -- Collect the argument names which the dynamic args depend on
    collectDDeps : NF [<] -> Core (List Name)
    collectDDeps (VBind tfc x (Pi _ _ _ nty) sc)
        = do defs <- get Ctxt
             sc' <- expand !(sc (pure (VApp tfc Bound x [<] (pure Nothing))))
             if x `elem` ns
                then collectDDeps sc'
                else do aty <- quote [<] nty
                        -- Get names depended on by nty
                        let deps = keys (getRefs (UN Underscore) aty)
                        rest <- collectDDeps sc'
                        pure (rest ++ deps)
    collectDDeps _ = pure []

    -- Return names the type depends on, and whether it's a parameter
    mutual
      getDepsArgs : Bool -> SnocList (NF [<]) -> NameMap Bool ->
                    Core (NameMap Bool)
      getDepsArgs inparam [<] ns = pure ns
      getDepsArgs inparam (as :< a) ns
          = do ns' <- getDeps inparam a ns
               getDepsArgs inparam as ns'

      getDeps : Bool -> NF [<] -> NameMap Bool ->
                Core (NameMap Bool)
      getDeps inparam (VLam _ x _ _ ty sc) ns
          = do defs <- get Ctxt
               ns' <- getDeps False !(expand ty) ns
               sc' <- expand !(sc (VErased fc Placeholder))
               getDeps False sc' ns
      getDeps inparam (VBind _ x (Pi _ _ _ pty) sc) ns
          = do defs <- get Ctxt
               ns' <- getDeps inparam !(expand pty) ns
               sc' <- expand !(sc (pure (VErased fc Placeholder)))
               getDeps inparam sc' ns'
      getDeps inparam (VBind _ x b sc) ns
          = do defs <- get Ctxt
               ns' <- getDeps False !(expand (binderType b)) ns
               sc' <- expand !(sc (pure (VErased fc Placeholder)))
               getDeps False sc' ns
      getDeps inparam (VApp _ Bound n args _) ns
          = do defs <- get Ctxt
               ns' <- getDepsArgs False !(traverseSnocList spineVal args) ns
               pure (insert n inparam ns')
      getDeps inparam (VDCon _ n t a args) ns
          = do defs <- get Ctxt
               getDepsArgs False !(traverseSnocList spineVal args) ns
      getDeps inparam (VTCon _ n a args) ns
          = do defs <- get Ctxt
               params <- case !(lookupDefExact n (gamma defs)) of
                              Just (TCon ti a) => pure (paramPos ti)
                              _ => pure []
               let (ps, ds) = splitPs 0 params
                                      (cast !(traverseSnocList spineVal args))
               ns' <- getDepsArgs True ps ns
               getDepsArgs False ds ns'
        where
          -- Split into arguments in parameter position, and others
          splitPs : Nat -> List Nat -> List (NF [<]) ->
                    (SnocList (NF [<]), SnocList (NF [<]))
          splitPs n params [] = ([<], [<])
          splitPs n params (x :: xs)
              = let (ps', ds') = splitPs (1 + n) params xs in
                    if n `elem` params
                       then (ps' :< x, ds')
                       else (ps', ds' :< x)
      getDeps inparam (VDelayed _ _ t) ns = getDeps inparam !(expand t) ns
      getDeps inparams nf ns = pure ns

    -- If the name of an argument is in the list of specialisable arguments,
    -- record the position. Also record the position of anything the argument
    -- depends on which is only dependend on by declared static arguments.
    collectSpec : List Nat -> -- specialisable so far
                  List Name -> -- things depended on by dynamic args
                               -- We're assuming  it's a short list, so just use
                               -- List and don't worry about duplicates.
                  List (Name, Nat) -> NF [<] -> Core (List Nat)
    collectSpec acc ddeps ps (VBind tfc x (Pi _ _ _ nty) sc)
        = do defs <- get Ctxt
             sc' <- expand !(sc (pure (VApp tfc Bound x [<] (pure Nothing))))
             if x `elem` ns
                then do deps <- getDeps True !(expand nty) NameMap.empty
                        -- Get names depended on by nty
                        -- Keep the ones which are either:
                        --  * parameters
                        --  * not depended on by a dynamic argument (the ddeps)
                        let rs = filter (\x => snd x ||
                                               not (fst x `elem` ddeps))
                                        (toList deps)
                        let acc' = insertDeps acc ps (x :: map fst rs)
                        collectSpec acc' ddeps ps sc'
                else collectSpec acc ddeps ps sc'
    collectSpec acc ddeps ps _ = pure acc

    getNamePos : Nat -> NF [<] -> Core (List (Name, Nat))
    getNamePos i (VBind tfc x (Pi _ _ _ _) sc)
        = do defs <- get Ctxt
             ns' <- getNamePos (1 + i) !(expand !(sc (pure (VErased tfc Placeholder))))
             pure ((x, i) :: ns')
    getNamePos _ _ = pure []
