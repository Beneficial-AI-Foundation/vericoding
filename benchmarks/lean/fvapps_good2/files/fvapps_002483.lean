-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_top_three_chars (s : String) : String :=
  sorry

def String.count (s : String) (c : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_top_three_chars_valid_format (s : String)
  (h : s.length > 0)
  (h2 : ∀ c ∈ s.data, c.isLower) :
  let result := get_top_three_chars s;
  let lines := result.splitOn "\n";
  1 ≤ lines.length ∧ lines.length ≤ 3 ∧
  (∀ line ∈ lines, ∃ (char : String) (count : Nat),
    line = s!"{char} {count}" ∧
    char.length = 1 ∧
    s.count char = count) ∧
  (∀ i < lines.length - 1,
    let parts1 := (lines.get! i).splitOn " ";
    let parts2 := (lines.get! (i+1)).splitOn " ";
    (parts1.get! 1).toNat! ≥ (parts2.get! 1).toNat!) ∧
  (let chars := lines.map (λ l => (l.splitOn " ").get! 0);
   chars.eraseDups = chars) :=
sorry

theorem get_top_three_chars_alphabetical_tiebreak (s : String)
  (h : s.length ≥ 2)
  (h2 : ∀ c ∈ s.data, c = 'a' ∨ c = 'b') :
  let result := get_top_three_chars s;
  let lines := result.splitOn "\n";
  ∀ i < lines.length - 1,
    let parts1 := (lines.get! i).splitOn " ";
    let parts2 := (lines.get! (i+1)).splitOn " ";
    let count1 := (parts1.get! 1).toNat!;
    let count2 := (parts2.get! 1).toNat!;
    let char1 := parts1.get! 0;
    let char2 := parts2.get! 0;
    count1 = count2 → char1 > char2 :=
sorry
-- </vc-theorems>