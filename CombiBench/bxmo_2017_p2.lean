import Mathlib

/--
Let \\( n \\geqslant 2 \\) be an integer. Alice and Bob play a game concerning a country made of \\( n \\) islands. Exactly two of those \\( n \\) islands have a factory. Initially there is no bridge in the country. Alice and Bob take turns in the following way. In each turn, the player must build a bridge between two different islands \\( I_{1} \\) and \\( I_{2} \\) such that:\n\n- \\( I_{1} \\) and \\( I_{2} \\) are not already connected by a bridge;\n- at least one of the two islands \\( I_{1} \\) and \\( I_{2} \\) is connected by a series of bridges to an island with a factory (or has a factory itself). (Indeed, access to a factory is needed for the construction.)\n\nAs soon as a player builds a bridge that makes it possible to go from one factory to the other, this player loses the game. (Indeed, it triggers an industrial battle between both factories.) If Alice starts, then determine (for each \\( n \\geqslant 2 \\)) who has a winning strategy.\n\n(Note: It is allowed to construct a bridge passing above another bridge.)
-/
theorem bxmo_2017_p2 : 1 = 1
    := by sorry
