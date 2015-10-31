module Parse (expr) where
import Text.Parsec
import Data.List

number :: Parsec String u Double
number = do
    i <- many1 digit
    f <- option "" $ (:) <$> char '.' <*> many1 digit
    return . read $ i ++ f

expr :: Parsec String u Double
expr = do
    initial <- term
    sum . (initial:) <$> many (
        (char '+' *> term)
        <|>
        (char '-' *> (negate <$> term))
                        )

term :: Parsec String u Double
term = do
    initial <- factor
    foldl' (\acc f -> f acc) initial <$> many (
                    ((*) <$> (char '*' *> factor))
                    <|>
                    (flip (/) <$> (char '/' *> factor))
                                              )

factor :: Parsec String u Double
factor = spaces *> (
            (char '(' *> expr <* char ')')
            <|>
            number
                   ) <* spaces
