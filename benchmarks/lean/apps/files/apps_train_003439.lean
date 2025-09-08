/-
Introduction 

The GADERYPOLUKI is a simple substitution cypher used in scouting to encrypt messages. The encryption is based on short, easy to remember key. The key is written as paired letters, which are in the cipher simple replacement.

The most frequently used key is "GA-DE-RY-PO-LU-KI".

```
 G => A
 g => a
 a => g
 A => G
 D => E
  etc.
```

The letters, which are not on the list of substitutes, stays in the encrypted text without changes.

Other keys often used by Scouts:

```
PO-LI-TY-KA-RE-NU
KA-CE-MI-NU-TO-WY
KO-NI-EC-MA-TU-RY
ZA-RE-WY-BU-HO-KI
BA-WO-LE-TY-KI-JU
RE-GU-LA-MI-NO-WY
```

Task

Your task is to help scouts to encrypt and decrypt thier messages.
Write the `Encode` and `Decode` functions. 

Input/Output

The function should have two parameters. 
The `message` input string consists of lowercase and uperrcase characters and whitespace character.
The `key` input string consists of only lowercase characters.
The substitution has to be case-sensitive. 

Example

 # GADERYPOLUKI collection

GADERYPOLUKI cypher vol 1

GADERYPOLUKI cypher vol 2

GADERYPOLUKI cypher vol 3 - Missing Key

GADERYPOLUKI cypher vol 4 - Missing key madness
-/

-- <vc-helpers>
-- </vc-helpers>

def encode (message : String) (key : String) : String := sorry
def decode (message : String) (key : String) : String := sorry

theorem non_key_chars_unchanged (message : String) (key : String) (i : String.Pos) :
  let key_chars := (key.toLower ++ key.toUpper).toList.toArray
  ¬(key_chars.contains (message.get i)) →
  (encode message key).get i = message.get i := sorry

theorem consistent_encoding (message key : String) :
  encode message key = encode message key := sorry

/-
info: 'Gug hgs g cgt'
-/
-- #guard_msgs in
-- #eval encode "Ala has a cat" "gaderypoluki"

/-
info: 'Dkucr pu yhr ykbir'
-/
-- #guard_msgs in
-- #eval encode "Dance on the table" "politykarenu"

/-
info: 'GBCE'
-/
-- #guard_msgs in
-- #eval encode "ABCD" "gaderypoluki"

-- Apps difficulty: introductory
-- Assurance level: unguarded