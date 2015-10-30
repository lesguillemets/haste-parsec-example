import Haste
import Haste.DOM
import Haste.Events
import Text.Parsec

main = do
    Just input <- elemById "calcInput"
    Just output <- elemById "output"
    onEvent input KeyUp $ \ e -> do
        Just l <- getValue input
        case parse p "" l of
             Right s -> setProp output "innerText" (unlines . map reverse $ s)
             Left _ -> return ()

p :: Parsec String u [String]
p = (many $ noneOf ",.!") `sepEndBy` (oneOf ",.!")
