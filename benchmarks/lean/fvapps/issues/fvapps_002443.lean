-- <vc-preamble>
def inner_product (v1 v2 : Vec Int) : Int := sorry 

def outer_product (v1 v2 : Vec Int) : Vec (Vec Int) := sorry

def vec_length {α : Type} (v : Vec α) : Nat :=
  match v with
  | Vec.nil => 0
  | Vec.cons _ rest => 1 + vec_length rest

def vec_sum_squares (v : Vec Int) : Int := sorry

def vec_transpose (m : Vec (Vec Int)) : Vec (Vec Int) := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vec_zip_with {α β γ : Type} (f : α → β → γ) : Vec α → Vec β → Vec γ := sorry

def vec_elem_prod (v1 v2 : Vec Int) : Int := sorry

-- Inner product equals element-wise product sum
-- </vc-definitions>

-- <vc-theorems>
theorem inner_product_equals_elemprod {v1 v2 : Vec Int} (h : vec_length v1 = vec_length v2) :
  inner_product v1 v2 = vec_elem_prod v1 v2 :=
sorry

-- Shape of outer product

theorem outer_product_dimensions {v1 v2 : Vec Int} :
  vec_length (outer_product v1 v2) = vec_length v1 :=
sorry

-- Inner product with self equals sum of squares 

theorem inner_product_self {v : Vec Int} :
  inner_product v v = vec_sum_squares v :=
sorry

-- Outer product transpose property

theorem outer_product_transpose_prop {v1 v2 : Vec Int} (h : vec_length v1 = vec_length v2) :
  outer_product v1 v2 = vec_transpose (outer_product v2 v1) :=
sorry
-- </vc-theorems>