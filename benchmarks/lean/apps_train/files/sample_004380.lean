The four bases found in DNA are adenine (A), cytosine (C), guanine (G) and thymine (T).

In genetics, GC-content is the percentage of Guanine (G) and Cytosine (C) bases on a DNA molecule that are either guanine or cytosine. 

Given a DNA sequence (a string) return the GC-content in percent, rounded up to 2 decimal digits for Python, not rounded in all other languages.

For more information about GC-content you can take a look to [wikipedia GC-content](https://en.wikipedia.org/wiki/GC-content).

**For example**: the GC-content of the following DNA sequence is 50%:
"AAATTTCCCGGG".

**Note**: You can take a look to my others bio-info kata [here](http://www.codewars.com/users/nbeck/authored)

def gc_content (s : String) : Float := sorry

theorem gc_content_bounded (s : String) :
  0.0 ≤ gc_content s ∧ gc_content s ≤ 100.0 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
