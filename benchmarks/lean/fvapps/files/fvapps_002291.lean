-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseWords (s : String) : String := sorry

theorem reverse_words_maintains_word_count {words : List String} (s : String) 
    (h : s = String.intercalate " " words) (h2 : ∀ w ∈ words, w.length > 0) : 
    (reverseWords s).splitOn.length = s.splitOn.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_words_maintains_word_length {words : List String} (s : String)
    (h : s = String.intercalate " " words) (h2 : ∀ w ∈ words, w.length > 0) :
    ∀ (orig rev : String), orig ∈ s.splitOn → rev ∈ (reverseWords s).splitOn →
    orig.length = rev.length := sorry

theorem double_reverse_is_identity (s : String) (h : s.length > 0) :
    reverseWords (reverseWords s) = s := sorry

theorem reverse_words_empty :
    reverseWords "" = "" := sorry
-- </vc-theorems>