module Main where
import Control.Monad

import Language.Haskell.Parser
import Language.Haskell.Pretty
import Language.Haskell.Syntax

import Front

main=do
    let f="./test/Sample.hs"
    xs<-readFile f
    
    
    let px=parseModuleWithMode (ParseMode f) xs
    
    case px of
        ParseFailed loc msg -> putStrLn ("@"++show loc) >> putStrLn msg
        ParseOk c ->
            print c >> putStrLn "\n==========\n" >>
            putStrLn (prettyPrint (mds $ wds c)) >>putStrLn "\n==========\n" >>
            print (mds $ wds c)












