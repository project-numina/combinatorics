import Mathlib.SetTheory.Cardinal.Basic
import Combinatorics.MyMultiset.Perm
import Combinatorics.MyMultiset.Comb
import Mathlib.Tactic.DeriveFintype
/-
An ice cream machine has 3 flavors - vanilla, chocolate, and strawberry.
The ice cream can be served in 2 ways - in a cone or in a cup. A
long with the ice cream, there are 5 options for toppings -
hot fudge, caramel, nuts, cherries, and sprinkles.
-/

open scoped Cardinal

inductive IceCream
| vanilla | chocolate | strawberry
deriving DecidableEq, Fintype

inductive Container
| cone | cup
deriving DecidableEq, Fintype

inductive Topping
| hotFudge | caramel | nuts | cherries | sprinkles
deriving DecidableEq, Fintype

structure IceCreamOrder where
  flavor : IceCream
  container : Container
  topping : Topping
  deriving DecidableEq, Fintype

example : Fintype.card IceCreamOrder = 30 := rfl

/-
A restaurant’s menu has 3 appetizers, 3 mains and 2 desserts.
In how many way can a 3-course meal be ordered?
-/

inductive Course
| appetizer | main | dessert
deriving DecidableEq, Fintype

def menu : MyMultiset Course where
  rep
  | .appetizer => 3
  | .main => 3
  | .dessert => 2

example : Fintype.card (menu.Comb 3) = 18 := sorry
