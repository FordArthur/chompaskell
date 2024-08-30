{-# LANGUAGE LambdaCase, TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Typechecker where

import Parser (TopLevel(..), Node(..))
import Control.Arrow
import Control.Lens
import Control.Monad.State
import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as S

type Constraints = [Node]
type Identificator = Node

data TypeError = TypeError -- ...

data Type =
    Variable    { varIdentifier :: Identificator  , constaints :: Constraints                     }
  | Constructor { constructor   :: Node           , typeArgs   :: [Type]                          }
  | Function    { takesType     :: Type           , retsType   :: Type        , fromClass :: Bool }
  deriving (Eq)

-- Checks if t1 and t2 are compatible
(~) :: Type -> Type -> Bool
t1 ~ t2 = undefined

data TypeContext =
  TypeContext {
    _functionContext :: H.HashMap String Type,
    _typeContext     :: H.HashMap String [Type],
    _classContext    :: H.HashMap String (H.HashMap String (S.HashSet (H.HashMap String Type)))
  }
makeLenses ''TypeContext

typeOfExpr :: Node -> StateT TypeContext (Either TypeError) Type
typeOfExpr = undefined

makeScopeContext :: [Node] -> H.HashMap String Type
makeScopeContext = H.fromList . map ((name . varIdentifier) &&& id) . zipWith (\c (Atom _ t p) -> Variable (Atom (c:"") t p) []) ['a'..'z']

typeOfImpl :: H.HashMap String Type -> [Node] -> StateT TypeContext (Either TypeError) Type
typeOfImpl = undefined

typeExprToType :: Node -> StateT TypeContext (Either TypeError) Type
typeExprToType = undefined

constrToType :: Node -> Type
constrToType = undefined

check :: TopLevel -> StateT TypeContext (Either TypeError) TopLevel
check bind@(VarBind vn vBind) = do
  typeOfBind <- typeOfExpr vBind
  bind <$ modify (over functionContext (H.insert (name vn) typeOfBind))

check impl@(Implementation fn args bodyV) = do
  typeOfThisImpl <- typeOfImpl (makeScopeContext args) bodyV
  typeOfFunc <- gets $ H.findWithDefault typeOfThisImpl (name fn) . _functionContext
  unless (typeOfThisImpl ~ typeOfFunc) $ void $ lift $ Left TypeError
  impl <$ modify (over functionContext (H.insert (name fn) typeOfFunc))

check decl@(Declaration dn dType) = do
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

checker :: [TopLevel] -> StateT TypeContext (Either TypeError) [TopLevel]
checker = traverse check . filter (\case { Infix -> False; _ -> True })
