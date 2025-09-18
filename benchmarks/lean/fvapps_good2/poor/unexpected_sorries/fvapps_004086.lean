def String.swap : String → String
  | _ => sorry

def Char.isVowel (c : Char) : Bool :=
  let vowels := ['a', 'e', 'i', 'o', 'u']
  sorry

theorem swap_preserves_length (s : String) :
  (String.swap s).length = s.length := sorry

theorem swap_idempotent (s : String) :
  String.swap (String.swap s) = String.swap s := sorry

theorem swap_preserves_non_vowels (s : String) (i : String.Pos) :
  ¬(Char.isVowel (s.get i)) →
  (String.swap s).get i = s.get i := sorry

theorem swap_capitalizes_vowels (s : String) (i : String.Pos) :
  (Char.isVowel (s.get i)) →
  ((String.swap s).get i).isUpper = true ∧
  ((String.swap s).get i).toLower = (s.get i).toLower := sorry

-- Apps difficulty: introductory
-- Assurance level: unguarded

/--
info: 'HEllOWOrld!'
-/
#guard_msgs in
#eval swap "HelloWorld!"

/--
info: 'SUndAy'
-/
#guard_msgs in
#eval swap "Sunday"

/--
info: 'AbrAcAdAbrA'
-/
#guard_msgs in
#eval swap "abracadabra"