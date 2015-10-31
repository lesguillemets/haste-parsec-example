import Haste
import Haste.DOM
import Haste.Events
import Text.Parsec

import Parse

main = do
    Just input <- elemById "calcInput"
    Just output <- elemById "output"
    onEvent input KeyUp $ \ e -> do
        Just ln <- getValue input
        case parse expr "" ln of
             Right s -> setProp output "innerText" (show s)
             Left l -> setProp output "innerText" (show l)
