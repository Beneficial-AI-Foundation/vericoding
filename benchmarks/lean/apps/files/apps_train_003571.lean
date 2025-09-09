-- <vc-helpers>
-- </vc-helpers>

def strange_coach (players : List String) : String := sorry

theorem strange_coach_sorted
  (players : List String)
  (h : strange_coach players ≠ "forfeit")
  (i j : Nat)
  (hi : i < (strange_coach players).length)
  (hj : j < (strange_coach players).length)
  (hij : i < j) :
  (strange_coach players).data[i] ≤ (strange_coach players).data[j] := sorry

theorem strange_coach_unique_chars
  (players : List String)
  (h : strange_coach players ≠ "forfeit")
  (i j : Nat)
  (hi : i < (strange_coach players).length)
  (hj : j < (strange_coach players).length)
  (hij : i < j) :
  (strange_coach players).data[i] ≠ (strange_coach players).data[j] := sorry

theorem strange_coach_forfeit_condition
  (players : List String) :
  strange_coach players = "forfeit" ↔
    ∀ c, (players.filter (λ p => p.get 0 = c)).length < 5 := sorry

theorem strange_coach_letter_condition
  (players : List String)
  (h : strange_coach players ≠ "forfeit")
  (c : Char) :
  c ∈ (strange_coach players).toList →
    (players.filter (λ p => p.get 0 = c)).length ≥ 5 := sorry

theorem strange_coach_complete
  (players : List String)
  (h : strange_coach players ≠ "forfeit")
  (c : Char) :
  (players.filter (λ p => p.get 0 = c)).length ≥ 5 →
    c ∈ (strange_coach players).toList := sorry

theorem strange_coach_output_nonempty
  (players : List String)
  (h : players ≠ []) :
  strange_coach players ≠ "" := sorry

theorem strange_coach_output_string
  (players : List String) :
  strange_coach players = "forfeit" ∨
  (∀ c ∈ (strange_coach players).toList, c.isAlpha) := sorry

/-
info: 'forfeit'
-/
-- #guard_msgs in
-- #eval strange_coach ["michael", "jordan", "lebron", "james", "kobe", "bryant"]

/-
info: 'bk'
-/
-- #guard_msgs in
-- #eval strange_coach ["babic", "keksic", "boric", "bukic", "sarmic", "balic", "kruzic", "hrenovkic", "beslic", "boksic", "krafnic", "pecivic", "klavirkovic", "kukumaric", "sunkic", "kolacic", "kovacic", "prijestolonasljednikovic"]

/-
info: 'b'
-/
-- #guard_msgs in
-- #eval strange_coach ["jgztazpytubijfsmjz", "bokvgratzzdibku", "qineboilzoqdqivc", "bfctyltibtkbxq", "vioxcuhqhikxeqwekqkjo", "nrvsdhttr", "eiaoajuwxpwmyliqikzcchid", "bxrwawgor", "gbsqaxotzmblxttj", "kwchrcaconuwaivhvnyf", "neiemapiica", "bppao", "bxujiwivsjfbqrzygpdgkyz", "jnzrhhmcgcpffflpzwmqib", "jhozlevckrrwimdmyzc", "bomojotkqqditelsk", "ywmbheywzfyqjjs", "snwrclyjkbspysjftcmyak", "eelrsgkuhu", "dnyzsvqjjuqoc"]

-- Apps difficulty: introductory
-- Assurance level: unguarded