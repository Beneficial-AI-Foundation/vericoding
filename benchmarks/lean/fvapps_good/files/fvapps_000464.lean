-- <vc-preamble>
def Word := String 
def Letter := Char

def Score := Nat

instance : OfNat Score n where
  ofNat := n

instance : Add Score := ⟨Nat.add⟩
instance : Mul Score := ⟨Nat.mul⟩
instance : LE Score := ⟨Nat.le⟩
instance : Inhabited Score := ⟨(0 : Score)⟩

instance : HMul Nat Score Score where
  hMul := fun n s => Nat.mul n s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_score_words (words: List Word) (letters: List Letter) (scores: List Score) : Score :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_score_words_non_negative (words: List Word) (letters: List Letter) (scores: List Score) :
  0 ≤ max_score_words words letters scores := sorry

theorem max_score_words_empty (letters: List Letter) (scores: List Score) : 
  max_score_words [] letters scores = 0 := sorry

theorem max_score_words_no_letters (words: List Word) (scores: List Score) :
  max_score_words words [] scores = 0 := sorry

theorem max_score_words_bounded (words: List Word) (letters: List Letter) (scores: List Score)
  (h: scores.length = 26) :
  max_score_words words letters scores ≤ letters.foldr (fun c acc => scores[Char.toNat c - Char.toNat 'a']! + acc) 0 := sorry

theorem single_letter_words_bounded (words: List Word) (letters: List Letter) (scores: List Score) 
  (h1: ∀ w ∈ words, w = "a") 
  (h2: ∀ l ∈ letters, l = 'a')
  (h3: scores.length = 26) :
  max_score_words words letters scores ≤ (min words.length letters.length) * (scores[0]!) := sorry

theorem impossible_words_zero_score (words: List Word) (letters: List Letter) (scores: List Score)
  (h1: ∀ letter ∈ letters, letter = 'x')
  (h2: ∃ w ∈ words, ∃ c ∈ w.data, c ≠ 'x')
  (h3: scores.length = 26) :
  max_score_words words letters scores = 0 := sorry
-- </vc-theorems>