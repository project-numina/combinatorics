import Mathlib

-- (n,k) where k ∈ {n, n+1, \ldots, \lceil \frac{3n}{2} \rceil}

/--
The Bank of Oslo issues two types of coin: aluminium (denoted A) and bronze (denoted B). Marianne has $n$ aluminium coins and $n$ bronze coins, arranged in a row in some arbitrary initial order. A chain is any subsequence of consecutive coins of the same type. Given a fixed positive integer $k\le 2n$, Marianne repeatedly performs the following operation: she identifies the longest chain containing the $k^{th}$ coin from the left, and moves all coins in that chain to the left end of the row. For example, if $n = 4$ and $k = 4$, the process starting from the ordering AABBBABA would be $AABBBABA \rightarrow BBBAAABA \rightarrow AAABBBBA \rightarrow BBBBAAAA \rightarrow BBBBAAAA \rightarrow \ldots$. Find all pairs $(n, k)$ with $1 \le k \le 2n$ such that for every initial ordering, at some moment during the process, the leftmost $n$ coins will all be of the same type.
-/
theorem imo_2022_p1 : 1 = 1 := by sorry
