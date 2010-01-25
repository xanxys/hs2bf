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
--            print c >> putStrLn "\n==========\n" >>
            putStrLn (prettyPrint (mds $ wds c)) >>putStrLn "\n==========\n" >>
            print (mds $ wds c)





{-

let
    x:xs=f x y e0
    z:zs=h x y
    y=g e1 z
in i x y z


let
    ts=(case ts of (x:xs,z:zs,y)->f x y e0
       ,case ts of (x:xs,z:zs,y)->h x y
       ,case ts of (x:xs,z:zs,y)->g e1 z
       )
in case ts of (x:xs,z:zs,y)->i x y z


-}
