import Mathlib

/-- 387
* Extend the deferred acceptance algorithm to the case in which there are more men than women. In such a case, not all of the men will get partners.
-/

-- Define the types of male and female.
-- Based on the requirements, it can be further expanded.
-- inductive male : Type
-- | M1 : male
-- | M2 : male
-- | M3 : male
-- | M4 : male
-- deriving DecidableEq

-- inductive female : Type
-- | W1 : female
-- | W2 : female
-- | W3 : female
-- deriving DecidableEq



-- -- Define a preference list.
-- -- A preference list is a mapping from males or females to the objects they prefer.
-- def preference_list (m : male) : List female :=
--   match m with
--   | male.M1 => [female.W1, female.W2, female.W3]  -- M1 的偏好顺序
--   | male.M2 => [female.W2, female.W3, female.W1]  -- M2 的偏好顺序
--   | male.M3 => [female.W3, female.W1, female.W2]  -- M3 的偏好顺序
--   | male.M4 => [female.W1, female.W2, female.W3]  -- M4 的偏好顺序


-- def preference_list_female (w : female) : List male :=
--   match w with
--   | female.W1 => [male.M1, male.M2, male.M3, male.M4]  -- W1 的偏好顺序
--   | female.W2 => [male.M2, male.M1, male.M3, male.M4]  -- W2 的偏好顺序
--   | female.W3 => [male.M3, male.M2, male.M1, male.M4]  -- W3 的偏好顺序


-- -- Define a pairing type: A mapping from females to males.
-- def pair : Type :=
--   female → Option male

-- -- Get the head of the linked list.
-- def get_head {α : Type} (l : List α) : Option α :=
--   match l with
--   | [] => none
--   | x :: _ => some x


-- -- Define the process of males making an application.
-- def propose (m : male) (w : female) (pairings : pair) : pair :=
--   match pairings w with
--   | none => -- If a female is not paired, she accepts the male's proposal.
--       λ w' => if w' = w then some m else pairings w'
--   | some m' => -- If a female is already paired
--       let pref_w := preference_list_female w
--       if m ∈ pref_w ∧ (m ∈ pref_w ∧ m ≠ m') then -- If the female prefers this male more
--         λ w' => if w' = w then some m else pairings w'
--       else pairings -- Otherwise, no changes are made.

-- -- Define a recursive function to simulate the proposal and matching process.
-- def matching_algorithm
--   (males : List male) (females : List female) (pairings : pair) : pair :=
--   match males with
--   | [] => pairings -- Define a recursive function to simulate the proposal and matching process.
--   | m :: ms =>
--       -- For the current male m, attempt to propose to the females he prefers.
--       let w := get_head (preference_list m)
--       match w with
--       | none => pairings
--       | some w =>
--         let new_pairings := propose m w pairings
--         matching_algorithm ms females new_pairings -- Recursively proceed to handle the next male.





-- Define male and female as indexed types based on the number.
def male := ℕ  -- Male is just a natural number (index).
deriving DecidableEq

def female := ℕ  -- Female is also a natural number (index).
deriving DecidableEq

-- A function to generate preference list for males.
def preference_list (m : male) (females : List female) : List female :=
  -- For simplicity, the preference list will just be a permutation of the females
  females.reverse -- This is a placeholder; in a real case, it would be more complex

-- A function to generate preference list for females.
def preference_list_female (w : female) (males : List male) : List male :=
  -- For simplicity, the preference list will just be a permutation of the males
  males.reverse -- This is a placeholder; in a real case, it would be more complex

-- Define a pairing type: A mapping from females to males (option).
def pair : Type := female → Option male

-- Get the head of the list (for proposing males).
def get_head {α : Type} (l : List α) : Option α :=
  match l with
  | [] => none
  | x :: _ => some x

-- Define the process of males making an application.
def propose (m : male) (w : female) (pairings : pair) (females : List female) (males : List male) : pair :=
  match pairings w with
  | none =>  -- If a female is not paired, she accepts the male's proposal.
      λ w' => if w' = w then some m else pairings w'
  | some m' =>  -- If a female is already paired
      let pref_w := preference_list_female w males
      if m ∈ pref_w ∧ (m ∈ pref_w ∧ m ≠ m') then  -- If the female prefers this male more
        λ w' => if w' = w then some m else pairings w'
      else pairings  -- Otherwise, no changes are made.

-- Define a recursive function to simulate the proposal and matching process.
def matching_algorithm
  (males : List male) (females : List female) (pairings : pair) : pair :=
  match males with
  | [] => pairings  -- All males have made their proposals.
  | m :: ms =>
      -- For the current male m, attempt to propose to the females he prefers.
      let w := get_head (preference_list m females)  -- Get the first female in the male's preference list.
      match w with
      | none => pairings  -- No females left to propose to.
      | some w =>
        let new_pairings := propose m w pairings females males  -- Propose to this female.
        matching_algorithm ms females new_pairings  -- Recursively proceed to handle the next male.



def run_matching (males : List male) (females : List female)
  (h : List.length males > List.length females) : pair :=
  let initial_pairings : pair := λ _ => none  -- No one is paired initially.
  matching_algorithm males females initial_pairings
