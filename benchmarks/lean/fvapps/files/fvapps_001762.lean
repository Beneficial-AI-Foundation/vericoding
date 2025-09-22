-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def display_table (orders : List (String × String × String)) : List (List String) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem display_table_empty (orders : List (String × String × String)) :
  orders = [] → display_table orders = [] :=
  sorry

theorem display_table_header (orders : List (String × String × String)) :
  orders ≠ [] → 
  match (display_table orders), (display_table orders).head? with
  | _, none => True
  | _, some h => match h.head? with
    | none => True
    | some x => x = "Table"
  :=
  sorry

theorem display_table_row_lengths (orders : List (String × String × String)) :
  orders ≠ [] →
  match (display_table orders).head? with
  | none => True
  | some first => ∀ row ∈ display_table orders, row.length = first.length :=
  sorry

theorem display_table_numeric_values (orders : List (String × String × String)) :
  orders ≠ [] →
  ∀ row ∈ List.tail (display_table orders),
  ∀ val ∈ List.tail row,
  ∀ c ∈ val.data,
  '0' ≤ c ∧ c ≤ '9' :=
  sorry

theorem display_table_sorted_tables (orders : List (String × String × String)) :
  orders ≠ [] →
  let table_nums := List.map (λ row => match row.head? with | none => "0" | some x => x) 
                    (List.tail (display_table orders))
  ∀ (i : Fin table_nums.length) (j : Fin table_nums.length), 
  i.val < j.val → 
  String.toNat! (table_nums.get i) ≤ String.toNat! (table_nums.get j) :=
  sorry

theorem display_table_sorted_items (orders : List (String × String × String)) :
  orders ≠ [] →
  match (display_table orders).head? with
  | none => True
  | some header => 
    let items := List.tail header
    ∀ (i : Fin items.length) (j : Fin items.length),
    i.val < j.val →
    items.get i ≤ items.get j :=
  sorry

theorem display_table_min_size (orders : List (String × String × String)) :
  orders ≠ [] →
  (display_table orders).length ≥ 2 ∧
  ∀ row ∈ display_table orders, row.length ≥ 2 :=
  sorry
-- </vc-theorems>