-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Post := Nat × Nat × String

def sort_posts (special_friends : List Nat) (posts : List Post) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_posts_length_matches_input 
  (special_friends : List Nat) (posts : List Post) :
  (sort_posts special_friends posts).length = posts.length :=
sorry

theorem sort_posts_preserves_contents
  (special_friends : List Nat) (posts : List Post) :
  ∀ s, (s ∈ (posts.map (fun p => p.2.2))) ↔ (s ∈ (sort_posts special_friends posts)) :=
sorry

theorem sort_posts_empty_posts
  (special_friends : List Nat) :
  sort_posts special_friends [] = [] :=
sorry

theorem sort_posts_order_preserved
  (special_friends : List Nat) (posts : List Post)
  (h_special : ∀ i j : Fin posts.length,
    special_friends.contains (posts[i].1) → 
    ¬special_friends.contains (posts[j].1) → 
    i < j) :
  ∀ i j : Fin posts.length,
    i < j →
    special_friends.contains (posts[i].1) =
    special_friends.contains (posts[j].1) →
    (posts[i].2.1 ≥ posts[j].2.1) :=
sorry
-- </vc-theorems>