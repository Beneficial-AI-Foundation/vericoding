-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greek_l33t (s : String) : String := sorry

theorem greek_l33t_length (s : String) :
  (greek_l33t s).length = s.length :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greek_l33t_lowercase (s : String) :
  (greek_l33t s).toLower = greek_l33t s := 
sorry

theorem greek_l33t_unmapped_unchanged (s : String) (i : String.Pos) : 
  let c := s.get i
  ¬(c.toLower ∈ ['a', 'b', 'd', 'e', 'i', 'k', 'n', 'o', 'p', 'r', 't', 'u', 'v', 'w', 'x', 'y']) →
  (greek_l33t s).get i = c.toLower :=
sorry

theorem greek_l33t_mapped_correct (s : String) (i : String.Pos) :
  let c := s.get i
  let mapping := [('a','α'), ('b','β'), ('d','δ'), ('e','ε'), ('i','ι'), ('k','κ'),
                 ('n','η'), ('o','θ'), ('p','ρ'), ('r','π'), ('t','τ'), ('u','μ'),
                 ('v','υ'), ('w','ω'), ('x','χ'), ('y','γ')]
  c.toLower ∈ mapping.map Prod.fst →
  (greek_l33t s).get i = (mapping.find? (fun p => p.1 = c.toLower)).get!.2 :=
sorry

theorem greek_l33t_idempotent (s : String) :
  greek_l33t (greek_l33t s) = greek_l33t s :=
sorry
-- </vc-theorems>