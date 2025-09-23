-- <vc-preamble>
def get_order (order: String) : String := sorry

def to_lower (s: String) : String := sorry

def to_capital (s: String) : String := sorry
def string_split (s: String) : List String := sorry

def menu_item_to_nat (m: MenuItem) : Nat :=
  match m with
  | .burger => 0
  | .fries => 1
  | .chicken => 2
  | .pizza => 3
  | .sandwich => 4
  | .onionrings => 5
  | .milkshake => 6
  | .coke => 7
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_to_menu_item? (s: String) : Option MenuItem := sorry

def string_eq_dec (s1 s2: String) : Decidable (s1 = s2) := inferInstance
-- </vc-definitions>

-- <vc-theorems>
theorem get_order_preserves_items (items: List MenuItem) (order: String) :
  let result := string_split (get_order order)
  ∀ item, items.contains item → result.contains (to_capital (toString item)) := sorry

theorem get_order_maintains_menu_order (items: List MenuItem) (order: String) : 
  let result := string_split (get_order order)
  ∀ s1 s2, result.contains s1 → result.contains s2 → ∀ m1 m2,
    string_to_menu_item? s1 = some m1 → 
    string_to_menu_item? s2 = some m2 →
    result.indexOf s1 ≤ result.indexOf s2 → 
    menu_item_to_nat m1 ≤ menu_item_to_nat m2 := sorry

theorem get_order_counts_match (items: List MenuItem) (order: String) :
  let result := string_split (get_order order)
  ∀ item: MenuItem, 
    (items.filter (fun x => x = item)).length = 
    (result.filter (fun x => to_lower x = toString item)).length := sorry

theorem get_order_only_valid_items (s: String) :
  let result := string_split (get_order s)
  ∀ item, result.contains item → ∃ m: MenuItem, to_lower item = toString m := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval get_order "burgerfriesfriesfriesfriesfriespizzasandwichcokefriesburger"

/-
info: expected2
-/
-- #guard_msgs in
-- #eval get_order "milkshakepizzachickenfriescokeburgerpizzasandwichmilkshakepizza"
-- </vc-theorems>