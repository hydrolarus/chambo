module Verification where

import           Control.Monad       (forM, forM_)
import           Control.Monad.Cont  (MonadIO (liftIO))
import           Control.Monad.State

import           Data.Char           (isSpace)
import           Data.List           (sortBy)
import qualified Data.Map            as M

import           Syntax

import           Z3.Monad

data VerificationCondition = VC
    { path        :: [String]
    , expression  :: Term
    , variables   :: [(String, Type)]
    , assumptions :: [Term]
    }
    deriving (Show)

data VerifyResult
    = Success
    | Unknown
    | Failed
        [(String, String)] -- counter-example, (var, value)
        VerificationCondition
    deriving (Show)


data TermEmitMode = Assume | Check

allVCs :: File -> [VerificationCondition]
allVCs file@(File items) = flip concatMap items $ \case
    IFunction func -> generateFunctionVCs file func

verify :: File -> VerificationCondition -> Z3 VerifyResult
verify file vc = do
    res <- checkVC file vc
    case res of
        (re, model) -> case re of
            Sat -> case model of
                Nothing -> pure $ Failed [] vc
                Just mo -> do
                    str <- modelToString mo
                    -- liftIO $ putStrLn str
                    let ce = parseModel str
                    pure $ Failed ce vc
            Unsat -> pure Success
            Undef -> pure Unknown

generateFunctionVCs :: File -> Function -> [VerificationCondition]
generateFunctionVCs file (Function _ args ret pres posts body Nothing) =
    error "Function not yet typechecked, this is a bug"
generateFunctionVCs file (Function name args ret pres posts body (Just tbody)) =
    let funs = map funcDecl $ functions file
        st = VCGenState
                { vcgPath = [name]
                , vcgVars = args
                , vcgAssumptions = pres
                , vcgVCs = []
                , vcgFile = file
                , vcgFunctions = funs
                , vcgPostconds = posts
                , vcgToplevel = True
                }
        ((), res) = flip runState st $ genVCs tbody
     in reverse $ vcgVCs res
    where
        funcDecl :: Function -> (String, [Type], Type)
        funcDecl (Function name args ret _ _ _ _) =
            let args' = sortBy (\(na, _) (nb, _) -> compare na nb) args
             in (name, map snd args', ret)


checkVC :: File -> VerificationCondition -> Z3 (Result, Maybe Model)
checkVC file vc = do
    goalExpr <- vcToSMT file vc
    -- goalExpr <- mkNot goalExpr'
    goal <- mkGoal False False False
    -- goalAssert goal goalExpr
    assert goalExpr
    str <- astToString goalExpr
    -- liftIO $ putStrLn str
    solverCheckAndGetModel


data VCGenState = VCGenState
    { vcgVars        :: [(String, Type)]
    , vcgAssumptions :: [Term]
    , vcgPostconds   :: [Term]
    , vcgFunctions   :: [(String, [Type], Type)]
    , vcgVCs         :: [VerificationCondition]
    , vcgFile        :: File
    , vcgToplevel    :: Bool
    , vcgPath        :: [String]
    }

type VCGenerator a = State VCGenState a

tellVC :: VerificationCondition -> VCGenerator ()
tellVC vc = modify $ \st@VCGenState {..} -> st {vcgVCs = vc : vcgVCs}

tellVar :: String -> Type -> VCGenerator ()
tellVar name ty = modify $ \st@VCGenState {..} -> st {vcgVars = (name, ty) : vcgVars}

localTerms :: ([Term] -> [Term]) -> VCGenerator a -> VCGenerator a
localTerms f action = do
    st@VCGenState {..} <- get
    put $ st {vcgAssumptions = f vcgAssumptions}
    res <- action
    modify $ \st -> st {vcgAssumptions = vcgAssumptions}
    pure res

localVar :: String -> Type -> VCGenerator a -> VCGenerator a
localVar name ty action = do
    st@VCGenState {..} <- get
    put $ st {vcgVars = (name, ty) : vcgVars}
    res <- action
    modify $ \st -> st {vcgVars = vcgVars}
    pure res

withPath :: String -> VCGenerator a ->VCGenerator a
withPath p action = do
    st@VCGenState {..} <- get
    put $ st {vcgPath = p : vcgPath}
    res <- action
    modify $ \st -> st {vcgPath = vcgPath}
    pure res

tellAssumption :: Term -> VCGenerator ()
tellAssumption t = modify $ \st@VCGenState {..} -> st {vcgAssumptions = t : vcgAssumptions}

makeVC :: Term -> VCGenerator ()
makeVC t = do
    st <- get
    let vc = VC {path = reverse (vcgPath st), expression = t, variables = vcgVars st, assumptions = vcgAssumptions st}
    tellVC vc

markResult :: TExpr -> VCGenerator ()
markResult e = do
    VCGenState {vcgPostconds} <- get
    withPath "post" $ forM_ (enumerate vcgPostconds) $ \(i, term) -> do
        let term' = substTerm (M.singleton "result" e) term
        withPath (show i) $ makeVC term'

isTop :: VCGenerator Bool
isTop = gets vcgToplevel

setTop :: Bool -> VCGenerator ()
setTop b = modify $ \st -> st {vcgToplevel = b}

withTopFalse :: VCGenerator a -> VCGenerator a
withTopFalse action = do
    top <- isTop
    setTop False
    res <- action
    setTop top
    pure res

done :: TExpr -> VCGenerator ()
done e = do
    top <- isTop
    if top
        then markResult e
        else pure ()

enumerate :: [a] -> [(Integer, a)]
enumerate = zip [1..]

genVCs :: TExpr -> VCGenerator ()
genVCs e@(TEIntLiteral n) = done e
genVCs e@(TEStringLiteral s) = done e
genVCs e@(TEBoolLiteral b) = done e
genVCs e@TEUnitLiteral = done e
genVCs e@(TEBinOp op a b) = do
    withTopFalse $ genVCs a
    withTopFalse $ genVCs b
    case op of
        OpDiv -> do
            let cond  = TEBinOp OpNeq b (TEIntLiteral 0)
                cond' = weakenExpr cond
                term = TExpr cond' (Just cond)
            withPath "div-rhs" $ makeVC term
        _ -> pure ()
    done e
genVCs e@(TEPrefixOp op a) = do
    genVCs a
    done e
genVCs (TESeq a b) = do
    withPath "seq-first" $ withTopFalse $ genVCs a
    withPath "seq-second" $ genVCs b
genVCs e@(TEVar s ty) = done e
genVCs f@(TEFunCall name args) = do
    let substs = M.fromList args
    let pathName = "call-" ++ show name

    withPath pathName $ forM_ args $ \(name, expr) ->
        withPath name $ withTopFalse $ genVCs expr

    VCGenState {vcgFile = file} <- get

    withPath pathName $ case lookupFunction file name of
        Nothing -> error $ "function \"" <> name <> "\" not available in File"
        Just (Function _ _ _ pres posts _ _) -> do

            withPath "pre" $ forM_ (enumerate pres) $ \(i, term) ->
                withPath (show i) $ makeVC $ substTerm substs term

            forM_ posts $ \term -> do
                let term' = substTerm (M.insert "result" f substs) term
                tellAssumption term'
    done f
genVCs (TEAssert te) = do
    withPath "assert-term" $
        withTopFalse $ genTermVCs te

    withPath "assert" $ makeVC te

    tellAssumption te
    done TEUnitLiteral
genVCs (TEIf cond thn els) = do
    withPath "if-cond" $ withTopFalse $ genVCs cond

    let notCond = TEPrefixOp OpNot cond
    let notCond' = weakenExpr notCond
    let cond' = weakenExpr cond
    let thn' = weakenExpr thn
    let els' = weakenExpr els

    localTerms (TExpr cond' (Just cond) :) $
        withPath "if-then" $ genVCs thn

    localTerms (TExpr notCond' (Just notCond) :) $
        withPath "if-else" $ genVCs els

genVCs (TELet s ty rhs body) = do
    let path = "let-" ++ s

    withPath path $ withPath "rhs" $
        withTopFalse $ genVCs rhs

    localVar s ty $ do
        let term = TEBinOp OpEq (TEVar s ty) rhs
            term' = weakenExpr term

        localTerms (TExpr term' (Just term) :) $
            withPath path $ withPath "body" $ genVCs body

genTermVCs :: Term -> VCGenerator ()
genTermVCs (TExpr ex Nothing) = error "Term not yet typechecked, this is a bug!"
genTermVCs (TExpr ex (Just te)) = genVCs te
genTermVCs (TForall s ty te) = do
    localVar s ty $ genTermVCs te
genTermVCs (TDisjunction a b) = do
    genTermVCs a
    genTermVCs b
genTermVCs (TConjunction a b) = do
    genTermVCs a
    genTermVCs b

vcToSMT :: File -> VerificationCondition -> Z3 AST
vcToSMT file v@VC {..} = do
    ctx <- initialCtx file
    vars <- forM variables $ \(name, ty) -> do
        ast <- varToSMT name ty
        pure (name, ast)

    let withCtx = withVars vars ctx

    withCtx $ \ctx -> do
        forM_ assumptions $ \term -> do
            ast <- termToSMT Assume ctx term
            assert ast

        termToSMT Check ctx expression

data VCCtx = VCCtx {vars :: [(String, AST)], funcs :: [(String, FuncDecl)]}

initialCtx :: File -> Z3 VCCtx
initialCtx file = do
    let funcs = functions file

    funcDecls <- forM funcs $ \(Function name args ret _ _ _ _) -> do
        let args' = sortBy (\(na, _) (nb, _) -> compare na nb) args
        sym <- mkStringSymbol name
        sorts <- forM args' (typeToSort . snd)
        ret' <- typeToSort ret
        decl <- mkFuncDecl sym sorts ret'
        pure (name, decl)

    pure $ VCCtx {vars = [], funcs = funcDecls}

withVariable :: String -> AST -> VCCtx -> (VCCtx -> a) -> a
withVariable name ast ctx f = f (ctx {vars = (name, ast) : vars ctx})

withVars :: [(String, AST)] -> VCCtx -> (VCCtx -> a) -> a
withVars [] ctx f = f ctx
withVars ((name, ast) : ns) ctx f = withVariable name ast ctx (\ctx -> withVars ns ctx f)

termMode :: TermEmitMode -> AST -> Z3 AST
termMode Check a  = mkNot a
termMode Assume a = pure a

termToSMT :: TermEmitMode -> VCCtx -> Term -> Z3 AST
termToSMT assum ctx (TExpr ex (Just ex')) = termMode assum =<< exprToSMT ctx ex'
termToSMT assum ctx (TExpr ex Nothing) = error "Term not yet type checked, this is a bug!"
termToSMT assum ctx (TForall s ty te) = do
    sort <- typeToSort ty
    name <- mkStringSymbol s
    var <- mkVar name sort
    t <- withVariable s var ctx $ \ctx -> do
            body <- termToSMT Assume ctx te
            mkForall [] [name] [sort] body

    termMode assum t
termToSMT assum ctx (TDisjunction a b) = do
    a' <- termToSMT Assume ctx a
    b' <- termToSMT Assume ctx b
    termMode assum =<< mkOr [a', b']
termToSMT assum ctx (TConjunction a b) = do
    a' <- termToSMT Assume ctx a
    b' <- termToSMT Assume ctx b
    termMode assum =<< mkAnd [a', b']

exprToSMT :: VCCtx -> TExpr -> Z3 AST
exprToSMT ctx (TEIntLiteral n) = mkInteger n
exprToSMT ctx (TEStringLiteral s) = mkString s
exprToSMT ctx (TEBoolLiteral b) = mkBool b
exprToSMT ctx TEUnitLiteral = mkInteger 0
exprToSMT ctx (TEBinOp op a b) = do
    a' <- exprToSMT ctx a
    b' <- exprToSMT ctx b
    binOpToSMT op a' b'
exprToSMT ctx (TEPrefixOp op a) = do
    a' <- exprToSMT ctx a
    prefixOpToSMT op a'
exprToSMT ctx (TESeq _ b) = exprToSMT ctx b
exprToSMT ctx (TEVar name ty) = case lookup name (vars ctx) of
    Nothing  -> error $ "undefined variable! " ++ show name ++ " this is a bug"
    Just ast -> pure ast
exprToSMT ctx (TEFunCall name args) = do
    let args' = sortBy (\(na, _) (nb, _) -> compare na nb) args
        argExprs = map snd args'

    argExprs' <- forM argExprs (exprToSMT ctx)

    case lookup name (funcs ctx) of
        Nothing -> error "undefined function! this is a bug"
        Just f  -> mkApp f argExprs'

exprToSMT ctx (TEAssert te) = mkInteger 0
exprToSMT ctx (TEIf cond t e) = do
    cond' <- exprToSMT ctx cond
    t' <- exprToSMT ctx t
    e' <- exprToSMT ctx e
    mkIte cond' t' e'
exprToSMT ctx (TELet s ty rhs body) = do
    -- we assume that the bound variable will be made into an declaration
    -- at the toplevel
    var <- varToSMT s ty
    withVariable s var ctx $ \c -> exprToSMT c body

binOpToSMT :: BinOp -> AST -> AST -> Z3 AST
binOpToSMT OpAdd     = \a b -> mkAdd [a, b]
binOpToSMT OpSub     = \a b -> mkSub [a, b]
binOpToSMT OpMul     = \a b -> mkMul [a, b]
binOpToSMT OpDiv     = mkDiv
binOpToSMT OpEq      = mkEq
binOpToSMT OpNeq     = \a b -> mkEq a b >>= mkNot
binOpToSMT OpLt      = mkLt
binOpToSMT OpLte     = mkLe
binOpToSMT OpGt      = mkGt
binOpToSMT OpGte     = mkGe
binOpToSMT OpImplies = mkImplies
binOpToSMT OpAnd     = \a b -> mkAnd [a, b]
binOpToSMT OpOr      = \a b -> mkOr [a, b]

prefixOpToSMT :: PrefixOp -> AST -> Z3 AST
prefixOpToSMT OpNot = mkNot

typeToSort :: Type -> Z3 Sort
typeToSort TInt    = mkIntSort
typeToSort TString = mkStringSort
typeToSort TBool   = mkBoolSort
typeToSort TUnit   = mkIntSort

varToSMT :: String -> Type -> Z3 AST
varToSMT name ty = do
    sort <- typeToSort ty
    symb <- mkStringSymbol name
    mkConst symb sort


-- TODO write a dedicated proper parser for the model output

parseModel :: String -> [(String, String)]
parseModel s = filter (/= ("", "")) $ go s
    where
        go [] = []
        go s  =
            let (ident, rest) = identAndRest s
                (val, rest')  = rhs rest
            in (ident, strip val) : go rest'


        identAndRest s =
            let (first, second) = break (== '-') s
                second' = drop 3 second
                first' = reverse $ drop 1 $ reverse first
             in (first', second')

        rhs [] = ("", "")
        rhs ('{':rest) =
            let (middle, '}':rest') = break (== '}') rest
            in (middle, rest')
        rhs s =
            let (val, '\n':rest') = break (== '\n') s
            in (val, rest')

        strip s = dropWhile isSpace . reverse . dropWhile isSpace $ reverse s

