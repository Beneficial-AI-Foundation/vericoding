/-
Your retro heavy metal band, VÄxën, originally started as kind of a joke, just because why would anyone want to use the crappy foosball table in your startup's game room when they could be rocking out at top volume in there instead? Yes, a joke, but now all the top tech companies are paying you top dollar to play at their conferences and big product-release events. And just as how in the early days of the Internet companies were naming everything "i"-this and "e"-that, now that VÄxënmänïä has conquered the tech world, any company that doesn't use Hëävÿ Mëtäl Ümläüts in ëvëry pössïblë pläcë is looking hopelessly behind the times.

Well, with great power chords there must also come great responsibility! You need to help these companies out by writing a function that will guarantee that their web sites and ads and everything else will RÖCK ÄS MÜCH ÄS PÖSSÏBLË! Just think about it -- with the licensing fees you'll be getting from Gööglë, Fäcëböök, Äpplë, and Ämäzön alone, you'll probably be able to end world hunger, make college and Marshall stacks free to all, and invent self-driving bumper cars. Sö lët's gët röckïng and röllïng! Pëdal tö thë MËTÄL!

Here's a little cheatsheet that will help you write your function to replace the so-last-year letters a-e-i-o-u-and-sometimes-y with the following totally rocking letters:

```
A = Ä = \u00c4     E = Ë = \u00cb     I = Ï = \u00cf
O = Ö = \u00d6     U = Ü = \u00dc     Y = Ÿ = \u0178
a = ä = \u00e4     e = ë = \u00eb     i = ï = \u00ef
o = ö = \u00f6     u = ü = \u00fc     y = ÿ = \u00ff
```
### Python issues
First, Python in the Codewars environment has some codec/encoding issues with extended ASCII codes like the umlaut-letters required above. With Python 2.7.6, when writing your solution you can just copy the above umlaut-letters (instead of the unicode sequences) and paste them into your code, but I haven't found something yet that will work for *both* 2.7.6 and 3.4.3 -- hopefully I will find something soon (answers/suggestions are welcome!), and hopefully that part will also be easier with other languages when I add them.

Second, along the same lines, don't bother trying to use string translate() and maketrans() to solve this in Python 2.7.6, because maketrans will see the character-mapping strings as being different lengths. Use a different approach instead.
-/

-- <vc-helpers>
-- </vc-helpers>

def heavy_metal_umlauts (s : String) : String := sorry

theorem length_preserved (s : String) :
  (heavy_metal_umlauts s).length = s.length := sorry

theorem non_vowels_unchanged (s : String) (i : Nat) (h : i < s.length) :
  let c := s.data[i]
  let h' : i < (heavy_metal_umlauts s).length := by rw [length_preserved s]; exact h
  c ∉ ['A', 'E', 'I', 'O', 'U', 'Y', 'a', 'e', 'i', 'o', 'u', 'y'] →
  (heavy_metal_umlauts s).data[i] = c := sorry

theorem idempotent (s : String) :
  heavy_metal_umlauts (heavy_metal_umlauts s) = heavy_metal_umlauts s := sorry

theorem no_vowels_in_result (s : String) :
  ∀ c ∈ String.toList (heavy_metal_umlauts s),
  c ∉ ['A', 'E', 'I', 'O', 'U', 'Y', 'a', 'e', 'i', 'o', 'u', 'y'] := sorry

/-
info: 'Ännöüncïng thë Mäcböök Äïr Güïtär'
-/
-- #guard_msgs in
-- #eval heavy_metal_umlauts "Announcing the Macbook Air Guitar"

/-
info: 'Fäcëböök'
-/
-- #guard_msgs in
-- #eval heavy_metal_umlauts "Facebook"

/-
info: 'Mëtäl'
-/
-- #guard_msgs in
-- #eval heavy_metal_umlauts "Metal"

-- Apps difficulty: introductory
-- Assurance level: unguarded