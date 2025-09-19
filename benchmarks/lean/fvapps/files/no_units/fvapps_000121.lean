-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_music_playlists (N L K : Nat) : Nat := sorry

theorem playlists_bounds (N L K : Nat) 
  (h1: N > 0) 
  (h2: L ≥ N) 
  (h3: K < N) :
  let result := num_music_playlists N L K
  0 ≤ result ∧ result < (10^9 + 7) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem playlists_k_eq_n_minus_one (N L K : Nat)
  (h1: N > 0)
  (h2: L ≥ N)
  (h3: K = N - 1) :
  num_music_playlists N L K > 0 := sorry

theorem playlists_trivial_cases_one_song :
  num_music_playlists 1 1 0 = 1 := sorry

theorem playlists_impossible_cases_one :
  num_music_playlists 1 2 1 = 0 := sorry 

theorem playlists_impossible_cases_two :
  num_music_playlists 2 4 2 = 0 := sorry
-- </vc-theorems>