/-
Chef changed the password of his laptop a few days ago, but he can't remember it today. Luckily, he wrote the encrypted password on a piece of paper, along with the rules for decryption.
The encrypted password is a string S consists of ASCII printable characters except space (ASCII 33 - 126, in decimal notation, the same below). Read here for more details: ASCII printable characters.
Each rule contains a pair of characters ci, pi, denoting that every character ci appears in the encrypted password should be replaced with pi. Notice that it is not allowed to do multiple replacements on a single position, see example case 1 for clarification.
After all the character replacements, the string is guaranteed to be a positive decimal number. The shortest notation of this number is the real password. To get the shortest notation, we should delete all the unnecessary leading and trailing zeros. If the number contains only non-zero fractional part, the integral part should be omitted (the shortest notation of "0.5" is ".5"). If the number contains zero fractional part, the decimal point should be omitted as well (the shortest notation of "5.00" is "5").
Please help Chef to find the real password.

-----Input-----
The first line of the input contains an interger T denoting the number of test cases.
The description of T test cases follows.
The first line of each test case contains a single interger N, denoting the number of rules.
Each of the next N lines contains two space-separated characters ci and pi,
denoting a rule.
The next line contains a string S, denoting the encrypted password.

-----Output-----
For each test case, output a single line containing the real password.

-----Constraints-----
- 1 ≤ T ≤ 1000
- 0 ≤ N ≤ 94
- All characters in S and ci may be any ASCII printable character except space. (ASCII 33 - 126)
- All ci in a single test case are distinct.
- pi is a digit ("0" - "9") or a decimal point "." (ASCII 46).
- The total length of S in a single input file will not exceed 106.

-----Example-----
Input:
4
2
5 3
3 1
5
0
01800.00
0
0.00100
3
x 0
d 3
# .
0xd21#dd098x

Output:
3
1800
.001
321.33098
-/

def decryptPassword (rules : List (Char × Char)) (encrypted : String) : String :=
  sorry

def stringToNat (s : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def replaceChar (s : String) (oldChar newChar : Char) : String :=
  sorry

theorem zero_rules_preserve_number {num : Nat} (h : num ≤ 1000000) :
  let encrypted := toString num
  let decrypted := decryptPassword [] encrypted
  stringToNat decrypted = num
  := sorry

theorem zero_rules_no_leading_zeros {num : Nat} (h : num ≤ 1000000) (h2 : num ≠ 0) :
  let encrypted := toString num  
  let decrypted := decryptPassword [] encrypted
  ¬(decrypted.get 0 = '0')
  := sorry

theorem zero_rules_single_zero :
  decryptPassword [] "0" = "0"
  := sorry

theorem simple_substitutions_preserve_number 
  {rules : List (Char × Char)} 
  {num : Nat}
  (h1 : num ≤ 1000000)
  (h2 : ∀ r1 r2, r1 ∈ rules → r2 ∈ rules → r1.1 = r2.1 → r1 = r2)
  (h3 : ∀ r, r ∈ rules → r.1 ∈ "abcdefghijklmnopqrstuvwxyz".data)
  (h4 : ∀ r, r ∈ rules → r.2 ∈ "0123456789".data)
  (h5 : rules.length ≤ 5) :
  let numStr := toString num
  let encrypted := rules.foldl (fun acc r => replaceChar acc r.2 r.1) numStr
  let decrypted := decryptPassword rules encrypted
  stringToNat decrypted = num
  := sorry

/-
info: '3'
-/
-- #guard_msgs in
-- #eval decrypt_password [("5", "3"), ("3", "1")] "5"

/-
info: '1800'
-/
-- #guard_msgs in
-- #eval decrypt_password [] "01800.00"

/-
info: '321.33098'
-/
-- #guard_msgs in
-- #eval decrypt_password [("x", "0"), ("d", "3"), ("#", ".")] "0xd21#dd098x"

-- Apps difficulty: interview
-- Assurance level: unguarded