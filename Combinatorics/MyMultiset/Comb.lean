import Combinatorics.MyMultiset.Basic

universe u

namespace MyMultiset

variable {α : Type u} (S : MyMultiset α)

structure Comb (n : ℕ) extends MyMultiset α where
  [rep_fin : toMyMultiset.RepIsFinite]
  [obj_fin : toMyMultiset.ObjIsFinite]
  rep_le (a : α) : toMyMultiset.rep a ≤ S.rep a
  card : toMyMultiset.card = n

namespace Comb

attribute [instance] Comb.rep_fin Comb.obj_fin

variable {S}

instance (n : ℕ) : Fintype (S.Comb n) := sorry

end Comb


end MyMultiset
