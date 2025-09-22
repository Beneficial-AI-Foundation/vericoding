-- <vc-preamble>
def listSum : List Nat → Nat
  | [] => 0
  | x::xs => x + listSum xs

def countChar (s: String) (c: Char) : Nat :=
  s.toList.filter (· == c) |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DIRS := [('←', (0,-1)), ('↑', (-1,0)), ('→', (0,1)), ('↓', (1,0)),
            ('↖', (-1,-1)), ('↗', (-1,1)), ('↘', (1,1)), ('↙', (1,-1))]

def count_deaf_rats (town: List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_output_range (town: List String)
  (h1: town.length > 0)
  (h2: listSum (town.map (fun row => countChar row 'P')) = 1)
  : let total_rats := listSum (town.map (fun row =>
      listSum ((DIRS.map Prod.fst).map (fun c => countChar row c))))
    let result := count_deaf_rats town
    0 ≤ result ∧ result ≤ total_rats :=
sorry

theorem empty_town :
  count_deaf_rats [" P "] = 0 :=
sorry

theorem simple_case :
  count_deaf_rats ["P →", "← ←"] = 2 :=
sorry

theorem all_directions :
  let dirChars := DIRS.map Prod.fst
  let town := ["P " ++ String.mk dirChars]
  let result := count_deaf_rats town
  0 ≤ result ∧ result ≤ DIRS.length :=
sorry
-- </vc-theorems>