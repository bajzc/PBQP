module Main (main) where

import Control.Monad (forM, forM_)
import Control.Monad.Reader as R
import Control.Monad.State
import Control.Monad.Writer as W
import Data.Map as M
import Solver (run)

main :: IO ()
main = print run

-- data E = C Int | V String | Add E E | Let String E E deriving (Show, Eq)

-- type Ctx = M.Map String Int

-- eval :: E -> Reader Ctx Int
-- eval (C v) = pure v
-- eval (V name) = do
--     m <- R.ask
--     pure (m M.! name)
-- eval (Add a b) = (+) <$> eval a <*> eval b
-- eval (Let name binding e) = do
--     val <- eval binding
--     R.local (M.insert name val) (eval e)

-- runEval :: E -> Int
-- runEval = flip runReader M.empty . eval

-- log :: String -> Writer [String] ()
-- log str = W.tell [str]

fib :: Int -> Int
fib 1 = 1
fib 2 = 1
fib n = fib (n - 1) + fib (n - 2)

f :: State Int ()
f = modify (+1)

g :: Int -> Int
g n = execState (do
        forM_ [1..n] $ const f
    ) n