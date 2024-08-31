{-# LANGUAGE LambdaCase, TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Typechecker where

import Parser (TopLevel(..), Node(..), AtomType(..))
import Data.Bool
import Control.Arrow
import Control.Lens
import Control.Monad.State
import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as S

type Constraints = [Node]
type Identificator = Node

data TypeError = TypeError -- ...

data MonoType =
    Variable    { varIdentifier :: Identificator                                                }
  | Constructor { constructor   :: Node           , typeArgs   :: [MonoType]                    }
  | Function    { takesType     :: MonoType       , retsType   :: MonoType  , fromClass :: Bool }
  deriving (Eq)

-- (Poly)Type
data Type = Mono MonoType | Quantified MonoType (S.HashSet Type)
  | Bottom -- Just for convenience

-- Checks if t1 and t2 are compatible
(~) :: Type -> Type -> Bool
t1 ~ t2 = undefined

data TheContext =
  TheContext {
    _functionContext :: H.HashMap String Type,
    _typeContext     :: H.HashMap String [Type],
    _classContext    :: H.HashMap String (H.HashMap String (S.HashSet (H.HashMap String Type)))
  }
makeLenses ''TheContext

proveVar :: Node -> StateT TheContext (Either TypeError) Type
proveVar (Atom n t _)
  | t == Identifier || t == TypeK = do
    fCtx <- gets _functionContext
    unless (n `H.member` fCtx) $ lift $ Left TypeError
    return $ H.findWithDefault Bottom n fCtx
  | t == Int                      = undefined -- builtin
  | t == Real'                    = undefined
proveVar _                        = undefined

proveFunc :: Type -> [Type] -> StateT TheContext (Either TypeError) Type
proveFunc =
  foldM $ \fType aType -> case fType of
    Mono (Function takeT retT _) -> bool (lift $ Left TypeError) (return . Mono $ retT) $ Mono takeT ~ aType
    _                            -> lift $ Left TypeError

makeScopeContext :: [Node] -> H.HashMap String Type
makeScopeContext = H.fromList . map ((name . varIdentifier) &&& Mono) . zipWith (\c (Atom _ t p) -> Variable (Atom (c:"") t p)) ['a'..'z']

typeOfExpr :: Node -> StateT TheContext (Either TypeError) Type
typeOfExpr atom@(Atom {})         = proveVar atom 
typeOfExpr (Expression e)         = mapM typeOfExpr e >>= uncurry proveFunc . (head &&& tail)
typeOfExpr (BinaryExpr e1 op' e2) = mapM typeOfExpr [op', e1, e2] >>= uncurry proveFunc . (head &&& tail)
typeOfExpr (LocalBind n e) = do
  eT <- typeOfExpr e
  modify $ functionContext `over` H.insert (name n) eT
  return eT
typeOfExpr (TypeAssertion e _ t)  = do
  eT <- typeOfExpr e
  tT <- typeExprToType t
  unless (eT ~ tT) $ lift $ Left TypeError
  return eT
typeOfExpr (ConcType {}) = undefined

typeExprToType :: Node -> StateT TheContext (Either TypeError) Type
typeExprToType = undefined

constrToType :: Node -> Type
constrToType = undefined

check :: TopLevel -> StateT TheContext (Either TypeError) TopLevel
check bind@(VarBind vn vBind) = do
  typeOfBind <- typeOfExpr vBind
  bind <$ modify (functionContext `over` H.insert (name vn) typeOfBind)

check impl@(Implementation fn args bodyV) = do
  tCtx' <- get
  modify $ functionContext `over` H.union (makeScopeContext args)
  typeOfThisImpl <- foldM (\_ n -> typeOfExpr n) Bottom bodyV
  put tCtx'
  typeOfFunc <- gets $ H.findWithDefault typeOfThisImpl (name fn) . _functionContext
  unless (typeOfThisImpl ~ typeOfFunc) $ void $ lift $ Left TypeError
  impl <$ modify (over functionContext (H.insert (name fn) typeOfFunc))

check decl@(Declaration dn dConstr dType) = do
  typeOfThisDecl <- typeExprToType dType
  typeOfFunc <- gets $ H.findWithDefault typeOfThisDecl (name dn) . _functionContext
  unless (typeOfThisDecl ~ typeOfFunc) $ void $ lift $ Left TypeError
  decl <$ modify (over functionContext (H.insert (name dn) typeOfFunc))

check dataD@(Data dn dArgs dConstr) = do
  tCtx <- gets _typeContext
  when (H.member (name dn) tCtx) $ void $ lift $ Left TypeError
  dataD <$ modify (over functionContext (flip (foldr (\constr m' -> H.insert (name $ concName constr) (constrToType constr) m')) dConstr)
                 . over typeContext (H.insert (name dn) (asTVar dArgs)))
  where asTVar = undefined

check instanceI@(Instance ing ied impls) = do
  iCtx <- gets _classContext
  case H.lookup (name ied) iCtx of
    Just class' -> case H.lookup (name ing) class' of { Nothing -> return (); Just _ -> void $ lift $ Left TypeError }
    Nothing     -> void $ lift $ Left TypeError
  _ <- verifyImpls iCtx impls
  return instanceI
  where verifyImpls = undefined

check classD@(Class cn cDecls) = do
  cCtx <- gets _classContext
  when (H.member (name cn) cCtx) $ void $ lift $ Left TypeError
  classHash <- classToHash cDecls
  classD <$ modify (over classContext (H.insert (name cn) (H.singleton "" classHash))) 
  where classToHash = undefined

check Infix = undefined

checker :: [TopLevel] -> StateT TheContext (Either TypeError) [TopLevel]
checker = traverse check . filter (\case { Infix -> False; _ -> True })
