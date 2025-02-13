import Mathlib

/--
An ice cream machine has 3 flavors - vanilla, chocolate, and strawberry. The ice cream can be served in 2 ways - in a cone or in a cup. Along with the ice cream, there are 5 options for toppings - hot fudge, caramel, nuts, cherries, and sprinkles.
-/
theorem easy_3 : Fintype.card (Fin 3 × Fin 2 × Fin 5) = 30 := by sorry
