{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Parser where

import Data.Functor ((<&>))
import Control.Arrow
import Text.Parsec
import Text.Parsec.Pos
import qualified Data.HashMap.Strict as H

data TopLevel a =
    Implementation { funcName         :: Node a, arguments    :: [Node a], body            :: [Node a]                    }
  | Declaration    { declName         :: Node a, constraintsD    :: H.HashMap String [Node a], declType     :: Node a     }
  | Data           { typeName         :: Node a, typeArgs     :: [Node a], constructors    :: [Node a]                    }
  | Instance       { instancing       :: Node a, instanced    :: Node a, implementations :: H.HashMap String [TopLevel a] }
  | Class          { className        :: Node a, declarations :: H.HashMap String [TopLevel a]                            }
  | Infix

data AtomType = Identifier | TypeK | Operator | Nat | Real' | Char' | String' | EndOfFile
  deriving (Eq, Show)

data Node a =
    Atom           { name       :: String, atomType    :: AtomType , info :: a , pos :: SourcePos        }
  | Lambda         { args       :: [Node a], lamExpr     :: Node a                                         }
  | Expression     { expression :: [Node a]                                                              }
  | BinaryExpr     { leftExpr   :: Node a, oper        :: Node a   , rightExpr   :: Node a               }
  | ConcType       { concName   :: Node a, consArgs    :: [Node a]                                       }
  | TypeAssertion  { node       :: Node a, constraints :: H.HashMap String [Node a], choritype :: Node a }
  | LocalBind      { locName    :: Node a, localBind   :: Node a                                         }
    deriving (Eq)

instance Show (Node a) where
  show (Atom n _ _ _)       = n
  show (Lambda a b)         = show "\\" ++ show a ++ " -> " ++ show b
  show (Expression [])      = undefined
  show (Expression (e:es))  = '(' : foldl (\s n -> s ++ ' ' : show n) (show e) es ++ ")"
  show (BinaryExpr le o re) = '(' : show o ++ " " ++ show le ++ " " ++ show re ++ ")"
  show (ConcType n a)       = show n ++ foldl (\s a' -> s ++ ' ' : show a') "" a
  show (TypeAssertion n c t)  = show n ++ " :: " ++ show c ++ " => "++ show t
  show (LocalBind v b)        = "let " ++ show v ++ " = " ++ show b

instance Show (TopLevel a) where
  show (Implementation f a b) = show f ++ ' ' : show a ++ " = " ++ show b
  show (Declaration f c t)    = show f ++ " :: " ++ show c ++ " => " ++ show t
  show (Data n a c)           = show n ++ show a ++ " with constructors " ++ show c
  show (Instance i c m)       = show i ++ " for " ++ show c ++ " where " ++ show m
  show (Class c d)            = show c ++ " where " ++ show d
  show Infix                  = ""

type Precedence = Int
type ParserState = (SourcePos, H.HashMap String Precedence)
type NoType = ()

atomWithName :: AtomType -> SourcePos -> String -> Node NoType
atomWithName t s n = Atom n t () s

scanChar :: (Monad m) => ParsecT String ParserState m Char -> ParsecT String ParserState m Char
scanChar p = do
  c <- p
  modifyState $ first (if c == '\n' then (`incSourceLine` 1) . (`setSourceColumn` 0) else (`incSourceColumn` 1))
  return c

parseEscapingChars :: (Monad m) => ParsecT String ParserState m Char
parseEscapingChars = scanChar (char '\\' >> escaping) <|> scanChar anyChar
  where escaping = oneOf "'\"\\nrtbfv" :: (Monad m) => ParsecT String ParserState m Char

parseChar :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseChar = do
  pos' <- fst <$> getState
  atomWithName Char' pos' . (: []) <$> between (char '\'') (char '\'') parseEscapingChars

parseString :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseString = do
  pos' <- fst <$> getState
  atomWithName String' pos' <$> between (char '\"') (char '\"') (many parseEscapingChars)

parseNum :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseNum = do
  pos' <- fst <$> getState
  int <- many1 $ scanChar digit
  dec <- option "" $ (:) <$> char '.' <*>  many1 digit
  return $ atomWithName (if null dec then Nat else Real') pos' $ int ++ dec

parseIdentifier :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseIdentifier = do
  pos' <- fst <$> getState
  initial <- scanChar lower
  atomWithName Identifier pos' . (initial :) <$> many (scanChar alphaNum)

parseTypeK :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseTypeK = do
  pos' <- fst <$> getState
  initial <- scanChar upper
  atomWithName TypeK pos' . (initial :) <$> many (scanChar alphaNum)

parseOp :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseOp = do
  pos' <- fst <$> getState
  atomWithName Operator pos' <$> many1 (scanChar $ oneOf "+-*/")

parseLambda :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseLambda = do
  _ <- char '\\' <|> char 'λ'
  spaces
  lambArgs <- many1 parseIdentifier
  spaces
  _ <- string "->"
  Lambda lambArgs <$> parseValueExpression

parseAtom :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseAtom = parseIdentifier <|> parseTypeK <|> between (char '(') (char ')') parseBinaryExpression <|> parseNum <|> parseChar <|> parseString

parseExpression :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseExpression = Expression <$> many1 (do {
  atom <- parseAtom;
  spaces;
  return atom
})

{- TODO: Infixl vs Infixr -}
parseBinaryExpression :: (Monad m) => ParsecT String ParserState m (Node NoType)
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
    addNode :: (Monad m) => H.HashMap String Int -> Node NoType -> Node NoType -> Node NoType -> m (Node NoType)
    addNode prec op  expr' expr= return $ insertNode (H.findWithDefault 5 (name op) prec) prec op expr' expr

    insertNode :: Int -> H.HashMap String Int -> Node NoType -> Node NoType -> Node NoType -> Node NoType
    insertNode _ _ op expr'@(Expression _) expr                         = BinaryExpr expr op expr'
    insertNode opPrec prec op expr'@(BinaryExpr lexpr' op' rexpr') expr = let opPrec' = H.findWithDefault 5 (name op') prec
                                                                            in if opPrec' > opPrec
                                                                                then BinaryExpr expr op expr'
                                                                                else BinaryExpr (insertNode opPrec prec op lexpr' expr) op' rexpr'
    insertNode _ _ _ _ _ = undefined

parseLocalBind :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseLocalBind = do
  _ <- string "let"
  spaces
  bindedName <- parseIdentifier
  spaces
  _ <- char '='
  spaces
  LocalBind bindedName <$> parseBinaryExpression

parseValueExpression :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseValueExpression = parseLocalBind <|> parseBinaryExpression <|> parseLambda

parseImplementation :: (Monad m) => ParsecT String ParserState m (TopLevel NoType)
parseImplementation = do
  fName <- parseIdentifier <|> parseOp
  spaces
  fArgs <- many $ parseIdentifier <* spaces
  _ <- char '='
  spaces
  bodyL <- parseValueExpression `sepBy` char ','
  _ <- char ';'
  return $ Implementation fName fArgs bodyL

parseConc :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseConc = do
  typeConstructor <- parseTypeK
  constructorArgs <- many $ parseIdentifier <|> between (char '(') (char ')') parseType
  return $ ConcType typeConstructor constructorArgs

parseType :: (Monad m) => ParsecT String ParserState m (Node NoType)
parseType = parseIdentifier <|> parseConc

parseConstraints :: (Monad m) => ParsecT String ParserState m (H.HashMap String [Node NoType])
parseConstraints = between (char '(') (char ')' >> spaces >> string "=>") $ parseConstraint `chainl1` (char ',' >> return (H.unionWith (++)))
  where
  parseConstraint = do {
    cnstraint <- parseTypeK;
    H.singleton (name cnstraint) . (: []) <$> parseIdentifier;
  }

parseTypeParser :: (Monad m) => ParsecT String ParserState m (Node NoType) -> ParsecT String ParserState m (Node NoType)
parseTypeParser p = do
  parsed <- p
  spaces
  _ <- string "::"
  spaces
  cnstraints <- option H.empty parseConstraints
  TypeAssertion parsed cnstraints . Expression <$> ((spaces *> parseType <* spaces) `sepBy` string "->") <* char ';'

parseDeclaration :: (Monad m) => ParsecT String ParserState m (TopLevel NoType)
parseDeclaration = (\(TypeAssertion e c t) -> Declaration e c t) <$> parseTypeParser (parseIdentifier <|> parseOp)

parseData :: (Monad m) => ParsecT String ParserState m (TopLevel NoType)
parseData = do
  _ <- string "data"
  spaces
  dataName <- parseIdentifier
  spaces
  dataArgs <- many (parseIdentifier <* spaces)
  _ <- char '='
  spaces
  Data dataName dataArgs <$> parseConc `sepBy` char '|'

parseInstance :: (Monad m) => ParsecT String ParserState m (TopLevel NoType)
parseInstance = do
  _ <- string "instance"
  spaces
  instancingClass <- parseIdentifier
  spaces
  instanceType <- parseIdentifier
  spaces
  Instance instancingClass instanceType <$> between (char '{') (char '}')
    ((parseImplementation <&> uncurry H.singleton . ((\(Instance n _ _) -> name n) &&& (: [])))
    `chainl1` (char ';' >> return (H.unionWith (++))))

parseClass :: (Monad m) => ParsecT String ParserState m (TopLevel NoType)
parseClass = do
  _ <- string "class"
  spaces
  classNaming <- parseIdentifier
  spaces
  Class classNaming <$> between (char '{') (char '}')
    ((parseDeclaration <&> uncurry H.singleton . ((\(Class n _) -> name n) &&& (: [])))
    `chainl1` (char ';' >> return (H.unionWith (++))))

parseInfix :: (Monad m) => ParsecT String ParserState m (TopLevel NoType)
parseInfix = do
  _ <- string "infix"
  spaces
  op <- parseOp
  spaces
  prec <- many1 digit
  spaces
  _ <- char ';'
  updateState $ second $ H.insert (name op) ((read :: String -> Int) prec)
  return Infix

parseFunc :: (Monad m) => ParsecT String ParserState m (TopLevel NoType)
parseFunc = parseImplementation <|> parseDeclaration

parseChoriLang :: (Monad m) => ParsecT String ParserState m [TopLevel NoType]
parseChoriLang = (parseFunc <|> parseData <|> parseDeclaration <|> parseInstance <|> parseClass <|> parseInfix) `sepBy` spaces

parser :: (Monad m) => String -> m (Either ParseError [TopLevel NoType])
parser = runParserT parseChoriLang (initialPos "CommandLine", H.empty) "CommandLine"
