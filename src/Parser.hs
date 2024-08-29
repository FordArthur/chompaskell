{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Parser where

import Control.Arrow
import Data.Functor ((<&>))
import Text.Parsec
import Text.Parsec.Pos
import qualified Data.HashMap.Strict as M

data TopLevel =
    Implementation { funcName         :: Node                     , arguments       :: [Node] , body :: [Node]     }
  | Declaration    { declName         :: Node                     , declType        :: Node                        }
  | Instance       { instancing       :: Node , instanced :: Node , implementations :: M.HashMap String [TopLevel] }
  | Class          { className        :: Node                     , declarations    :: M.HashMap String [TopLevel] }
  | Infix

data AtomType = Identifier | TypeK | Operator | Int | Real' | EndOfFile
  deriving (Eq, Show)

data Node =
    Atom           { name             :: String               , atomType  :: AtomType, pos       :: SourcePos }
  | Expression     { expression       :: [Node]                                                               }
  | BinaryExpr     { leftExpr         :: Node                 , oper      :: Node,     rightExpr :: Node      }
  | VarType        { constraintsNodes :: [Node]               , absName   :: Node                             }
  | ConcType       { concName         :: Node                 , consArgs  :: [Node]                           } 
  | TypeAssertion  { node             :: Node                 , choritype :: Node                             }
  | VarBind        { varname          :: Node                 , bind      :: Node                             }
    deriving (Eq)

instance Show Node where
  show (Atom n _ _)         = n
  show (Expression [])      = undefined
  show (Expression (e:es))  = foldl (\s n -> s ++ ' ' : show n) (show e) es
  show (BinaryExpr le o re) = show o ++ " (" ++ show le ++ ") (" ++ show re ++ ")"
  show (VarType c n)        = show n ++ " ∈ " ++ show c
  show (ConcType n a)       = show n ++ (foldl1 (\s s' -> s ++ ' ' : s') . map show $ a)
  show (TypeAssertion n t)  = show n ++ " :: " ++ show t
  show (VarBind v b)        = "let " ++ show v ++ " = " ++ show b

data Error = Err { errMsg :: String, errPos :: SourcePos }
  deriving (Show)

type Precedence = Int
type ParserState = (SourcePos, M.HashMap String Precedence)

atomWithName :: AtomType -> SourcePos -> String -> Node
atomWithName t s n = Atom n t s

scanChar :: (Monad m) => ParsecT String ParserState m Char -> ParsecT String ParserState m Char
scanChar p = do
  c <- p
  modifyState $ first (if c == '\n' then (`incSourceLine` 1) . (`setSourceColumn` 0) else (`incSourceColumn` 1))
  return c

parseNum :: (Monad m) => ParsecT String ParserState m Node
parseNum = do
  pos' <- fst <$> getState
  int <- many1 $ scanChar digit
  dec <- option "" $ (:) <$> char '.' <*>  many1 digit
  return $ atomWithName (if null dec then Int else Real') pos' $ int ++ dec

parseIdentifier :: (Monad m) => ParsecT String ParserState m Node
parseIdentifier = do
  pos' <- fst <$> getState
  initial <- scanChar lower
  atomWithName Identifier pos' . (initial :) <$> many (scanChar alphaNum)

parseTypeK :: (Monad m) => ParsecT String ParserState m Node
parseTypeK = do
  pos' <- fst <$> getState
  initial <- scanChar upper
  atomWithName TypeK pos' . (initial :) <$> many (scanChar alphaNum)

parseOp :: (Monad m) => ParsecT String ParserState m Node
parseOp = do
  pos' <- fst <$> getState
  atomWithName Operator pos' <$> many1 (scanChar $ oneOf "+-*/")

parseAtom :: (Monad m) => ParsecT String ParserState m Node
parseAtom = parseIdentifier <|> parseTypeK <|> do { _ <- char '('; val <- parseBinaryExpression; _ <- char ')'; return val} <|> parseNum

parseExpression :: (Monad m) => ParsecT String ParserState m Node
parseExpression = Expression <$> many1 (do {
  atom <- parseAtom;
  spaces;
  return atom
})

{- TODO: Infixl vs Infixr -}
parseBinaryExpression :: (Monad m) => ParsecT String ParserState m Node
parseBinaryExpression = do
  expr <- parseExpression
  spaces
  mkRest <- do {
    op <- parseOp;
    spaces;
    expr' <- parseBinaryExpression;
    prec <- snd <$> getState;
    return $ addNode prec op expr'
  }  <|> return return
  mkRest expr
  where
    addNode :: (Monad m) => M.HashMap String Int -> Node -> Node -> Node -> m Node
    addNode prec op  expr' expr= return $ insertNode (M.findWithDefault 5 (name op) prec) prec op expr' expr

    insertNode :: Int -> M.HashMap String Int -> Node -> Node -> Node -> Node
    insertNode _ _ op expr'@(Expression _) expr                         = BinaryExpr expr op expr'
    insertNode opPrec prec op expr'@(BinaryExpr lexpr' op' rexpr') expr = let opPrec' = M.findWithDefault 5 (name op') prec
                                                                            in if opPrec' > opPrec
                                                                                then BinaryExpr expr op expr'
                                                                                else BinaryExpr (insertNode opPrec prec op lexpr' expr) op' rexpr'
    insertNode _ _ _ _ _ = undefined

parseBind :: (Monad m) => ParsecT String ParserState m Node
parseBind = do
  _ <- string "let"
  spaces
  bindedName <- parseIdentifier
  spaces
  _ <- char '='
  spaces
  VarBind bindedName <$> parseBinaryExpression

parseValueExpression :: (Monad m) => ParsecT String ParserState m Node
parseValueExpression = parseBind <|> parseBinaryExpression

parseImplementation :: (Monad m) => ParsecT String ParserState m TopLevel
parseImplementation = do
  fName <- parseIdentifier
  spaces
  args <- many $ parseIdentifier <* spaces
  bodyL <- parseValueExpression `sepBy` char ','
  _ <- char ';'
  return $ Implementation fName args bodyL

parseType :: (Monad m) => M.HashMap String [Node] -> ParsecT String ParserState m Node
parseType constraints = uncurry VarType . ((flip (M.lookupDefault []) constraints . name) &&& id) <$> parseIdentifier <|> do
  typeConstructor <- parseTypeK
  constructorArgs <- many $ parseIdentifier <|> between (char '(') (char ')') (parseType constraints)
  return $ ConcType typeConstructor constructorArgs

parseConstraints :: (Monad m) => ParsecT String ParserState m (M.HashMap String [Node])
parseConstraints = between (char '(') (char ')' >> spaces >> string "=>") $ parseConstraint `chainl1` (char ',' >> return (M.unionWith (++)))
  where
  parseConstraint = do {
   cnstraint <- parseTypeK;
    boundedVar <- parseIdentifier;
    return $ M.singleton (name cnstraint) [boundedVar]
  }

parseTypeExpression :: (Monad m) => ParsecT String ParserState m Node
parseTypeExpression = do
  _ <- string "::"
  spaces
  cnstraints <- option M.empty parseConstraints
  spaces
  Expression <$> many1 (parseType cnstraints <* spaces)

parseDeclaration :: (Monad m) => ParsecT String ParserState m TopLevel
parseDeclaration = do
  declFuncName <- parseIdentifier
  spaces
  Declaration declFuncName <$> parseTypeExpression

parseInstance :: (Monad m) => ParsecT String ParserState m TopLevel
parseInstance = do
  _ <- string "instance"
  spaces
  instancingClass <- parseIdentifier
  spaces
  instanceType <- parseIdentifier
  spaces
  Instance instancingClass instanceType <$> between (char '{') (char '}') 
    ((parseImplementation <&> uncurry M.singleton . ((\(Instance n _ _) -> name n) &&& (: []))) 
    `chainl1` (char ';' >> return (M.unionWith (++))))

parseClass :: (Monad m) => ParsecT String ParserState m TopLevel
parseClass = do
  _ <- string "class"
  spaces
  classNaming <- parseIdentifier
  spaces
  Class classNaming <$> between (char '{') (char '}') 
    ((parseDeclaration <&> uncurry M.singleton . ((\(Class n _) -> name n) &&& (: [])))
    `chainl1` (char ';' >> return (M.unionWith (++))))

parseInfix :: (Monad m) => ParsecT String ParserState m TopLevel
parseInfix = do
  _ <- string "infix"
  spaces
  op <- parseOp
  spaces
  prec <- many1 digit
  spaces
  _ <- char ';'
  updateState $ second $ M.insert (name op) ((read :: String -> Int) prec)
  return Infix

parseChoriLang :: (Monad m) => ParsecT String ParserState m TopLevel
parseChoriLang = parseImplementation <|> parseDeclaration <|> parseInstance <|> parseClass <|> parseInfix

parser :: (Monad m) => String -> m (Either ParseError Node)
parser = runParserT parseBinaryExpression (initialPos "CommandLine", M.empty) "CommandLine"
