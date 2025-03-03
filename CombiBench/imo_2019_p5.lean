import Mathlib

-- $\frac{n(n+1)}{4}$

variable (n : ℕ)

abbrev Coin := Fin 2

abbrev Coin.H : Coin := 0

abbrev Coin.T : Coin := 1

abbrev CoinConfig := Fin (n + 1) → Coin

variable {n}

def CoinConfig.countH (c : CoinConfig n) : ℕ := (List.ofFn c).count .H

def CoinConfig.flip (c : CoinConfig n) (k : Fin (n + 1)) : CoinConfig n :=
  Function.update c k (c k).rev

def CoinConfig.update (c : CoinConfig n) : Option (CoinConfig n) :=
  if c.countH = 0 then none else
  .some <| c.flip ⟨c.countH.pred, by
    have := (List.ofFn c).count_le_length .H
    rw [Nat.lt_succ, Nat.pred_le_iff]
    simpa only [List.length_ofFn] using (List.ofFn c).count_le_length .H⟩

def CoinConfig.updateMultipleTimes (c : CoinConfig n) : ℕ → Option (CoinConfig n)
  | 0 =>
    if c.countH = 0 then none else .some c
  | k+1 => c.updateMultipleTimes k >>= update


def CoinConfig.L (c : CoinConfig n) : ℕ := sorry

def CoinConfig.L_spec (c : CoinConfig n) : c.updateMultipleTimes c.L = .none := sorry

def CoinConfig.L_min (c : CoinConfig n) : ∀ (n : ℕ), n < c.L → c.updateMultipleTimes n ≠ .none := sorry

/--
The Bank of Bath issues coins with an $H$ on one side and a $T$ on the other. Harry has $n$ of these coins arranged in a line from left to right. He repeatedly performs the following operation: If there are exactly $k > 0$ coins showing $H$, then he turns over the $k^{th}$ coin from the left; otherwise, all coins show $T$ and he stops. For example, if $n = 3$ the process starting with the configuration $THT$ would be $THT \rightarrow HHT \rightarrow HTT \rightarrow TTT$, which stops after three operations. (a) Show that, for each initial configuration, Harry stops after a finite number of operations. (b) For each initial configuration $C$, let $L(C)$ be the number of operations before Harry stops. For example, $L(THT) = 3$ and $L(TTT) = 0$. Determine the average value of $L(C)$ over all $2^n$ possible initial configurations $C$.
-/
theorem imo_2019_p5_a : ∀ (c : CoinConfig n), ∃ N : ℕ, c.updateMultipleTimes N = .none := sorry

def imo_2019_p5_b_sol : ℕ → ℚ := sorry

theorem imo_2019_p5_b : (imo_2019_p5_b_sol n = ∑ c : CoinConfig n, (c.L : ℚ) / (Fintype.card (CoinConfig n))) := sorry
