import Data.Graph (vertices)
import Data.List (find)
import Data.Map (Map, insert, (!))
import Data.Map qualified as Map
import Data.Bifunctor (first)

type Vertex = String

data Cost = Finite Int | Inf deriving (Read)

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

-- Show instance: show Inf as "inf", Finite as number
instance Show Cost where
  show Inf = "inf"
  show (Finite x) = show x

data Register = Reg Int | Spill deriving (Show, Read, Ord, Eq)

type CostV = [Cost]

type CostM = [[Cost]]

type Edge = (Vertex, Vertex)

type CostF = (Map Vertex CostV, Map Edge CostM)

type Solution = Map Vertex Register

type Stack a = [a]

type Graph = ([Vertex], [Edge], CostF)

adj :: Graph -> Vertex -> [Vertex]
adj (_, es, _) v = [to | (from, to) <- es, from == v]

deg :: Graph -> Vertex -> Int
deg (_, es, _) v = length [() | (from, _) <- es, from == v]

remove :: (Eq a) => a -> [a] -> [a]
remove element = filter (/= element)

addCost :: Cost -> Cost -> Cost
addCost Inf _ = Inf
addCost _ Inf = Inf
addCost (Finite a) (Finite b) = Finite (a + b)

addCostM :: CostM -> CostM -> CostM
addCostM = zipWith addCostV

addCostV :: CostV -> CostV -> CostV
addCostV = zipWith addCost

findFirstMin :: (Ord a) => [a] -> Int
findFirstMin xs = let x = minimum xs in head $ map fst (filter ((== x) . snd) (zip [0 ..] xs))

spillCost :: Int
spillCost = 1000

reduceI :: Graph -> Solution -> Vertex -> (Graph, Solution)
reduceI g@(vs, es, (w, w2)) s x =
  let y = head $ adj g x
      cx = w ! x
      cy = w ! y
      delta :: [Cost] = map (minimum . addCostV cx) (w2 ! (y, x))
      cy' = addCostV delta cy
   in ((remove x vs, remove (x, y) es, (insert y cy' w, w2)), s)

reduceII :: Graph -> Solution -> Vertex -> (Graph, Solution)
reduceII g@(vs, es, (w, w2)) s x =
  let [y, z] = adj g x
      cyx = w2 ! (y, x)
      czx = w2 ! (z, x)
      cyz = w2 ! (y, z)
      cx = w ! x
      delta :: [[Cost]] = [[minimum $ zipWith3 (\a b c -> addCost a (addCost b c)) i j cx | j <- czx] | i <- cyx]
      es' = remove (x, z) $ remove (x, y) es
   in case find (== (y, z)) es of
        Just _ -> ((remove x vs, es', (w, insert (y, z) (addCostM cyz delta) w2)), s)
        Nothing -> ((remove x vs, (y, z) : es', (w, insert (y, z) delta w2)), s)

reduceN :: Graph -> Solution -> Vertex -> (Graph, Solution)
reduceN g@(vs, es, f@(w, w2)) s x =
  let cx = w ! x
      c :: [Cost] = map (\i -> foldl (\ci y -> ci `addCost` minimum (addCostV ((w2 ! (x, y)) !! i) (w ! y))) (Finite 0) (adj g x)) [0 .. length cx - 1]
      -- no forbidden assignments
      s' = insert x (Reg $ findFirstMin c) s
      vs' = remove x vs
      es' :: [Edge] = foldl (\es y -> remove (x, y) es) es (adj g x)
      (c', (w', w2')) :: ([Cost], CostF) =
        foldl
          ( \(c, (w, w2)) y ->
              let cxy = w2 ! (x, y)
                  (Reg sx) = s ! x
                  (xs, csx : ys) = splitAt sx cxy
                  csx' = map (`replace` deg g x) csx
                  c' = zipWith (\a b -> (if b == Inf then replace b (deg g x) else a)) c csx
                  cxy' = xs ++ csx' : ys
                  cy = addCostV (w ! y) c'
               in (c', (insert y cy w, insert (x, y) cxy' w2))
          )
          (c, f)
          (adj g x)
   in ((vs', es', (w', w2')), s')
  where
    replace :: Cost -> Int -> Cost
    replace Inf deg = Finite $ spillCost `div` deg
    replace c _ = c

-- vertices of degree of n
dns :: Graph -> Int -> Maybe [Vertex]
dns g@(vs, _, _) n = let res = filter (\v -> deg g v == n) vs in if null res then Nothing else Just res

reduceGraph :: Graph -> Solution -> Stack Vertex -> (Graph, Solution, Stack Vertex)
reduceGraph g@(_, [], _) s svs = (g, s, svs) -- no more edges
reduceGraph g@(vs, es, f) s svs =
  case dns g 0 of
    Just (v0 : _ ) ->
      reduceGraph (remove v0 vs, es, f) s svs
    Nothing -> case dns g 1 of
      Just (v1 : _) ->
        -- Bucket 1 (degree 1)
        let (g', s') = reduceI g s v1
        in reduceGraph g' s' (v1 : svs)
      Nothing -> case dns g 2 of
        Just (v2 : _) ->
          -- Bucket 2 (degree 2)
          let (g', s') = reduceII g s v2
          in reduceGraph g' s' (v2 : svs)
        Nothing -> case vs of
          (v : _) ->
            -- Any other vertex
            let (g', s') = reduceN g s v
            in reduceGraph g' s' (v : svs)
          [] -> (g, s, svs) -- No vertices left

propagateSolution :: [Vertex] -> Graph -> Solution -> Stack Vertex -> Solution
propagateSolution vs g@([], es, f@(w, w2)) s svs =
  let s' = foldl (\c x -> insert x (Reg $ findFirstMin (w ! x)) c) s vs
   in go svs s g
  where
    go :: Stack Vertex -> Solution -> Graph -> Solution
    go [] s _ = s
    go (x : svs) s g@(_, _, (w, w2)) =
      let c = foldl (\c y -> addCostV c [let (Reg sx) = s ! x in cs !! sx | cs <- w2 ! (y, x)]) (w ! x) (adj g x)
       in go svs (insert x (Reg (findFirstMin c)) s) g

----------------------

regs :: [Register]
regs = Spill : [Reg i | i <- [0 .. 9]]

regsClass :: [(Register, Char)]
regsClass = (Spill, 's') : [(Reg i, 'a') | i <- [0 .. 3]] ++ [(Reg i, 'i') | i <- [4 .. 5]] ++ [(Reg i, 'f') | i <- [6 .. 9]]

-- spilling costs
s :: Int -> CostV
s cost = map (\x -> if x == Spill then Inf else Finite 0) regs

-- class constrain
c :: Register -> CostV
c reg = let i = lookup reg regsClass in map (\x -> if lookup x regsClass == i then Finite 0 else Inf) regs

-- copy propagation
r :: Int -> Register -> CostV
r c reg = map (\x -> if x == reg then Finite (-c) else Finite 0) regs

symRegs :: [Vertex]
symRegs = ["sa0", "sa1", "sa2", "sn0", "sn1", "sn2", "sfl0", "sf1", "sf2"]

costVEmpty :: [Cost]
costVEmpty = map (const $ Finite 0) regs

fsEmpty :: [(Vertex, CostV)]
fsEmpty = [(v, costVEmpty) | v <- symRegs]

fs :: Map Vertex CostV
fs =
  Map.fromList $
    fsEmpty
      ++ [ ("sa0", addCostV (s 110) (c $ Reg 0)),
           ("sa1", addCostV (s 110) (c $ Reg 1)),
           ("sa2", addCostV (s 110) (addCostV (c $ Reg 2) (r 5 $ Reg 2))),
           ("sn0", addCostV (s 110) (c $ Reg 3)),
           ("sn1", addCostV (s 100) (c $ Reg 4)),
           ("sn2", addCostV (s 100) (c $ Reg 5)),
           ("sfl0", addCostV (s 220) (c $ Reg 6)),
           ("sf1", addCostV (s 200) (c $ Reg 6)),
           ("sf2", addCostV (s 200) (c $ Reg 6))
         ]

-- interference constraint of two symbolic registre
i :: CostM
i = [[if a /= b || a == Spill then Finite 0 else Inf | b <- regs] | a <- regs]

costMEmpty :: [[Cost]]
costMEmpty = [[Finite 0 | b <- regs] | a <- regs]

fss :: Map Edge CostM
fss = let t =  [(("sa0", "sa1"), i), (("sa0", "sa2"), i), (("sa1", "sa2"), i)] in Map.fromList $ fssEmpty ++ t -- ++ map (first (uncurry (flip (,)))) t -- ((a,b) ,c) -> ((b,a),c)

fssEmpty :: [(Edge, CostM)]
fssEmpty = [((i, j), costMEmpty) | i <- symRegs, j <- symRegs]

isZeros :: CostM -> Bool
isZeros = all (all (== Finite 0))

edges :: [Edge]
edges = filter (\x -> not $ isZeros $ fss ! x) [(i, j) | i <- symRegs, j <- symRegs]

run :: Solution
run = let (g, s, svs) = reduceGraph (symRegs, edges , (fs, fss)) Map.empty [] in propagateSolution symRegs g s svs

main :: IO ()
main = print run