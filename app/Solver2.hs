{-# LANGUAGE BlockArguments #-}

module Solver2 (run) where

import Control.Arrow ((***))
import Control.Monad (join, unless)
import Control.Monad qualified
import Control.Monad.State
import Data.Bifunctor (Bifunctor (first))
import Data.List (delete, elemIndex, find, sortBy, (\\))
import Data.Map (Map, insert, (!))
import Data.Map qualified as Map
import Data.Maybe (fromJust, fromMaybe)
import Data.Tuple (swap)

newtype Vertex = Vertex String deriving (Show, Eq, Ord)

data Cost = Finite Int | Inf deriving (Show)

instance Eq Cost where
  Inf == Inf = True
  Finite x == Finite y = x == y
  _ == _ = False

-- Ordering: Inf > any Finite, Inf == Inf
instance Ord Cost where
  compare Inf Inf = EQ
  compare Inf _ = GT
  compare _ Inf = LT
  compare (Finite x) (Finite y) = compare x y

data Register = Reg Int | Spill deriving (Show, Read, Ord, Eq)

type CostV = [Cost]

type CostM = [CostV]

type Edge = (Vertex, Vertex)

type CostF = (Map Vertex CostV, Map Edge CostM)

type Solution = Map Vertex Register

-- undirected graph, but keeps edges in both directions
type Graph = ([Vertex], [Edge])

type Stack = [Vertex]

type Ctx = (Graph, Stack, CostF)

adj :: Graph -> Vertex -> [Vertex]
adj (_, es) v = [to | (from, to) <- es, from == v]

degree :: Graph -> Vertex -> Int
degree = (length .) . adj

addCost :: Cost -> Cost -> Cost
addCost Inf _ = Inf
addCost _ Inf = Inf
addCost (Finite a) (Finite b) = Finite (a + b)

addCostV :: CostV -> CostV -> CostV
addCostV = zipWith addCost

addCostM :: CostM -> CostM -> CostM
addCostM = zipWith addCostV

removeVertex :: Vertex -> [Edge] -> [Edge]
removeVertex _ [] = []
removeVertex x (e@(from, to) : es) = if from == x || to == x then removeVertex x es else e : removeVertex x es

-- push x to stack and remove the vertex from graph
pushVertex :: Vertex -> State Ctx ()
pushVertex x = modify (\((vs, es), s, c) -> ((delete x vs, removeVertex x es), x : s, c))

findFirstMin :: (Ord a) => [a] -> Int
findFirstMin xs = let x = minimum xs in head $ map fst (filter ((== x) . snd) (zip [0 ..] xs))

matrixColumn :: [[a]] -> Int -> [a]
matrixColumn m j = [row !! j | row <- m]

transpose :: [[a]] -> [[a]]
transpose ([] : _) = []
transpose x = map head x : transpose (map tail x)

updateCostM :: Edge -> CostM -> Map Edge CostM -> Map Edge CostM
updateCostM e m = Map.union (Map.fromList [(e, m), (swap e, transpose m)])

-- call with the only adj vertex y of x
reduceI :: Vertex -> Vertex -> State Ctx ()
reduceI x y = do
  pushVertex x
  (g, s, (w, w2)) <- get
  let cx = w ! x
      cy = w ! y
      cyx = w2 ! (y, x)
      delta = map (minimum . addCostV cx) cyx
   in put (g, s, (insert y (addCostV cy delta) w, w2))

reduceII :: Vertex -> Vertex -> Vertex -> State Ctx ()
reduceII x y z = do
  pushVertex x
  (g@(vs, es), s, (w, w2)) <- get
  let cyx = w2 ! (y, x)
      czx = w2 ! (z, x)
      cyz = w2 ! (y, z)
      cx = w ! x
      delta = [[minimum $ addCostV i (addCostV j cx) | j <- czx] | i <- cyx]
   in case find (== (y, z)) es of
        Just _ -> put (g, s, (w, updateCostM (y, z) (addCostM cyz delta) w2))
        Nothing -> put ((vs, (y, z) : (z, y) : es), s, (w, updateCostM (y, z) delta w2))

sortGraph :: State Ctx ()
sortGraph = do
  (g@(vs, es), c, f) <- get
  put ((sortBy (\a b -> compare (degree g a) (degree g b)) vs, es), c, f)

-- require: vertices are sorted by their degree
reduceGraph :: State Ctx ()
reduceGraph = do
  sortGraph
  (g@(_, es), stack, f) <- get
  case fst g of
    [] -> pure ()
    (v : vs) ->
      case adj g v of
        [] -> put ((vs, es), stack, f)
        [y] -> reduceI v y
        [y, z] -> reduceII v y z
        _ -> undefined
  unless (null $ fst g) reduceGraph

propagateSolution :: [Vertex] -> Ctx -> State Solution ()
propagateSolution vs1 (g@(vs2, _), stack, (w, w2)) = do
  mapM_ (\x -> modify (insert x (assignReg $ findFirstMin (w ! x)))) (vs1 \\ vs2)
  mapM_ (\x -> modify (\solution -> insert x (assignReg $ findFirstMin $ foldl (\c y -> addCostV c $ matrixColumn (w2 ! (y, x)) $ regIndex (solution ! x)) (w ! x) (adj g x)) solution)) stack

----------------------

regs :: [Register]
regs = Spill : [Reg i | i <- [0 .. 4]]

assignReg :: Int -> Register
assignReg i = regs !! i

regIndex :: Register -> Int
regIndex r = fromJust $ elemIndex r regs

regsClass :: [(Register, Char)]
regsClass = (Spill, 's') : [(Reg i, 'a') | i <- [0 .. 2]] ++ [(Reg i, 'b') | i <- [3..4]]

-- spilling costs
spillCostF :: Int -> CostV
spillCostF cost = map (\x -> if x == Spill then Inf else Finite cost) regs

-- class constrain
classConstrainF :: Register -> CostV
classConstrainF reg = let i = lookup reg regsClass in map (\x -> if lookup x regsClass == i then Finite 0 else Inf) regs

-- copy propagation
copyPropF :: Int -> Register -> CostV
copyPropF c reg = map (\x -> if x == reg then Finite (-c) else Finite 0) regs

symRegs :: [Vertex]
symRegs = Vertex <$> ["sa0", "sa1", "sa2"] -- "sn0", "sn1", "sn2", "sfl0", "sf1", "sf2"

costVEmpty :: [Cost]
costVEmpty = map (const $ Finite 0) regs

fsEmpty :: [(Vertex, CostV)]
fsEmpty = [(v, costVEmpty) | v <- symRegs]

fs :: Map Vertex CostV
fs =
  Map.fromList $
    fsEmpty
      ++ [ (Vertex "sa0", addCostV (spillCostF 110) (classConstrainF $ Reg 0)),
           (Vertex "sa1", addCostV (spillCostF 110) (classConstrainF $ Reg 1)),
           (Vertex "sa2", addCostV (spillCostF 110) (addCostV (classConstrainF $ Reg 2) (copyPropF 5 $ Reg 2)))
           --  (Vertex "sn0", addCostV (spillCostF 110) (classConstrainF $ Reg 3)),
           --  (Vertex "sn1", addCostV (spillCostF 100) (classConstrainF $ Reg 4)),
           --  (Vertex "sn2", addCostV (spillCostF 100) (classConstrainF $ Reg 5)),
           --  (Vertex "sfl0", addCostV (spillCostF 220) (classConstrainF $ Reg 6)),
           --  (Vertex "sf1", addCostV (spillCostF 200) (classConstrainF $ Reg 6)),
           --  (Vertex "sf2", addCostV (spillCostF 200) (classConstrainF $ Reg 6))
         ]

-- interference constraint of two symbolic registre
interferenceCostM :: CostM
interferenceCostM = [[if a /= b || a == Spill then Finite 0 else Inf | b <- regs] | a <- regs]

costMEmpty :: [[Cost]]
costMEmpty = [[Finite 0 | _ <- regs] | _ <- regs]

edges :: [Edge]
edges = [(Vertex "sa0", Vertex "sa1"), (Vertex "sa1", Vertex "sa2"), (Vertex "sa0", Vertex "sa2")]

diEdges :: [Edge]
diEdges = edges ++ map swap edges

fss :: Map Edge CostM
fss = Map.fromList $ fssEmpty ++ map (,interferenceCostM) diEdges

fssEmpty :: [(Edge, CostM)]
fssEmpty = [((i, j), costMEmpty) | i <- symRegs, j <- symRegs, i /= j]

initCtx :: Ctx
initCtx = ((symRegs, diEdges), [], (fs, fss))

run :: Solution
run =
  evalState
    ( do
        reduceGraph
        ((vs, _), stack, f) <- get
        pure $ execState (propagateSolution symRegs ((vs, diEdges), stack, f)) Map.empty
    )
    initCtx
