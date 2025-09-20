-- <vc-preamble>
def Sorted (as : List Nat) : Prop :=
  ∀ i j, i < j → j < as.length → as[i]! < as[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_time (n m : Nat) (heads tracks : List Nat) : Nat := sorry

theorem find_min_time_non_negative (n m : Nat) (heads tracks : List Nat)
  (h1 : heads.length = n)
  (h2 : tracks.length = m)
  (h3 : Sorted heads)
  (h4 : Sorted tracks) :
  find_min_time n m heads tracks ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_time_perfect_alignment (n m : Nat) (heads tracks : List Nat)
  (h1 : heads.length = n)
  (h2 : tracks.length = m)
  (h3 : Sorted heads)
  (h4 : Sorted tracks)
  (h5 : ∀ t ∈ tracks, t ∈ heads) :
  find_min_time n m heads tracks = 0 := sorry

theorem find_min_time_monotonic_heads (n m : Nat) (heads tracks : List Nat) 
  (new_head : Nat)
  (h1 : heads.length = n)
  (h2 : tracks.length = m)
  (h3 : Sorted heads)
  (h4 : Sorted tracks)
  (h5 : ∀ h ∈ heads, h < new_head) :
  find_min_time (n+1) m (heads ++ [new_head]) tracks ≤ 
  find_min_time n m heads tracks := sorry

theorem find_min_time_monotonic_tracks (n m : Nat) (heads tracks : List Nat)
  (new_track : Nat)
  (h1 : heads.length = n)
  (h2 : tracks.length = m)
  (h3 : Sorted heads)
  (h4 : Sorted tracks)
  (h5 : ∀ t ∈ tracks, t < new_track) :
  find_min_time n (m+1) heads (tracks ++ [new_track]) ≥
  find_min_time n m heads tracks := sorry
-- </vc-theorems>