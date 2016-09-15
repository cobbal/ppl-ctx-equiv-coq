module Main where
import Test.QuickCheck
import Data.Int

type Var = Int8
type Env a = [(Var, a)]

lkup :: Env a -> Var -> Maybe a
lkup [] _ = Nothing
lkup ((x, v) : ρ') x' = if x == x' then Just v else lkup ρ' x'

extend :: Env a -> Var -> a -> Env a
extend ρ x v = (x, v) : ρ

for_all :: (Bounded a, Enum a) => (a -> Bool) -> Bool
for_all p = all p [minBound ..]

domain :: Env a -> [Var]
domain = map fst

env_compat :: Env Var -> Env Var -> Bool
env_compat ρ0 ρ1 =
  for_all $ \ x0 ->
  for_all $ \ x1 ->
  (lkup ρ0 x0 == Just x1) == (lkup ρ1 x1 == Just x0)

extendable :: Env Var -> Env Var -> Var -> Var -> Bool
extendable ρ0 ρ1 x0 x1 = if env_compat ρ0 ρ1
                         then env_compat (extend ρ0 x0 x1) (extend ρ1 x1 x0)
                         else True

main = do
  let ρ0 = [(0, 1)]
  let ρ1 = [(1, 0)]
  print $ env_compat ρ0 ρ1
  print $ extendable ρ0 ρ1 0 0
  -- quickCheck extendable
  -- quickCheckWith stdArgs { maxSuccess = 500 } extendable
