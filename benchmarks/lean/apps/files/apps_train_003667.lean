/-
Your back at your newly acquired decrypting job for the secret organization when a new assignment comes in.   Apparently the enemy has been communicating using a device they call "The Mirror".  
It is a rudimentary device with encrypts the message by switching its letter with its mirror opposite (A => Z), (B => Y), (C => X) etc.  

Your job is to build a method called "mirror" which will decrypt the messages. Resulting messages will be in lowercase.

To add more secrecy, you are to accept a second optional parameter, telling you which letters or characters are to be reversed; if it is not given, consider the whole alphabet as a default.

To make it a bit more clear: e.g. in case of "abcdefgh" as the second optional parameter, you replace "a" with "h", "b" with "g" etc. .

For example:
```python
mirror("Welcome home"), "dvoxlnv slnv" #whole alphabet mirrored here
mirror("hello", "abcdefgh"), "adllo" #notice only "h" and "e" get reversed
```
-/

-- <vc-helpers>
-- </vc-helpers>

def mirror (s : String) (alphabet : String := "abcdefghijklmnopqrstuvwxyz") : String := sorry

theorem double_mirror_returns_original (s : String) :
  mirror (mirror s) = s.toLower := sorry

theorem mirror_identity_with_empty_chars (s : String) :
  mirror s "" = s.toLower := sorry

theorem empty_string_mirror :
  mirror "" = "" ∧ mirror "" "" = "" := sorry

theorem mirror_preserves_non_mapped_chars :
  mirror "123!@#" "abc" = "123!@#" := sorry

theorem basic_mirror :
  mirror "abcxyz" = "zyxcba" := sorry

/-
info: 'dvoxlnv slnv'
-/
-- #guard_msgs in
-- #eval mirror "Welcome home"

/-
info: 'adllo'
-/
-- #guard_msgs in
-- #eval mirror "hello" "abcdefgh"

/-
info: 'this is a secret'
-/
-- #guard_msgs in
-- #eval mirror "gsrh rh z hvxivg"

-- Apps difficulty: introductory
-- Assurance level: unguarded