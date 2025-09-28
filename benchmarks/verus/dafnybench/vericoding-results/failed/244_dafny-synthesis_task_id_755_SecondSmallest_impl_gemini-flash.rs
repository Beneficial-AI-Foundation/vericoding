use vstd::prelude::*;

verus! {

spec fn min_pair(s: Seq<i32>) -> i32 {
    if s[0] <= s[1] { s[0] } else { s[1] }
}

spec fn min(s: Seq<i32>) -> i32;

// <vc-helpers>
spec fn min(s: Seq<i32>) -> i32 {
    if s.len() == 0 {
        0 // Should not happen given preconditions
    } else if s.len() == 1 {
        s[0]
    } else {
        min_pair(Seq::new(2, |i| {
            if i == 0 { s[0] } else { min(s.subsequence(1, s.len())) }
        }))
    }
}

proof fn lemma_min_is_min_of_all_elements(s: Seq<i32>)
    requires s.len() > 0
    ensures forall |i: int| 0 <= i < s.len() ==> s[i] >= min(s)
    ensures exists |i: int| 0 <= i < s.len() && s[i] == min(s)
{
    if s.len() == 1 {
        assert(s[0] == min(s));
    } else {
        let m_tail = min(s.subsequence(1, s.len()));
        lemma_min_is_min_of_all_elements(s.subsequence(1, s.len()));
        // For the `s[0] <= m_tail` case:
        // We know min(s) == s[0].
        // We need to show s[i] >= s[0] for all i.
        // For i=0, s[0] >= s[0] is trivial.
        // For i>0, we know s[i] >= m_tail from recursive call's ensurers.
        // Since s[0] <= m_tail, we have s[i] >= m_tail >= s[0].
        // For existence, s[0] == min(s).
        
        // For the `s[0] > m_tail` case:
        // We know min(s) == m_tail.
        // We need to show s[i] >= m_tail for all i.
        // For i=0, s[0] > m_tail, so s[0] >= m_tail.
        // For i>0, s[i] >= m_tail from recursive call's ensurers.
        // For existence, we know exists j in [1, len) s.t. s[j] == m_tail.
        // Since min(s) == m_tail, this s[j] serves as the witness.

        // The assertions in the original code are essentially what Verus would deduce
        // from the lemma's end-states IF it could handle the `min_pair` definition
        // directly. Since it can't fully, we need to ensure the recursive call's
        // postconditions are used correctly.
        // The key is that the ensurers of this lemma are for `s`, not its subsequences directly.
        // The recursive call `lemma_min_is_min_of_all_elements(s.subsequence(1, s.len()))`; 
        // establishes its own ensurers for `s.subsequence(1, s.len())`.

        // Prove the first ensurer: forall |i: int| 0 <= i < s.len() ==> s[i] >= min(s)
        assert forall |i: int| 0 <= i < s.len() implies s[i] >= min(s) by {
            if i == 0 {
                // Case s[0] <= m_tail: min(s) is s[0]. Then s[0] >= s[0] is true.
                // Case s[0] > m_tail: min(s) is m_tail. Then s[0] > m_tail, so s[0] >= m_tail is true.
            } else {
                // i > 0, so consider s.subsequence(1, s.len())
                // By recursive call, s.subsequence(1, s.len())[i-1] >= min(s.subsequence(1, s.len()))
                // which means s[i] >= m_tail.
                if s[0] <= m_tail { // min(s) == s[0]
                    assert(s[i] >= m_tail); // from recursive call
                    assert(m_tail >= s[0]); // by assumption
                    assert(s[i] >= s[0]); // transitive
                } else { // min(s) == m_tail
                    assert(s[i] >= m_tail); // from recursive call
                }
            }
        }

        // Prove the second ensurer: exists |i: int| 0 <= i < s.len() && s[i] == min(s)
        if s[0] <= m_tail {
            // In this case, min(s) == s[0]. The witness is i=0.
            assert(s[0] == min(s));
            assert(exists |i: int| 0 <= i < s.len() && s[i] == min(s));
        } else {
            // In this case, min(s) == m_tail.
            // By recursive call, there exists j_tail such that 0 <= j_tail < s.subsequence(1, s.len()).len()
            // and s.subsequence(1, s.len())[j_tail] == m_tail.
            // This means there exists j such that 1 <= j < s.len() and s[j] == m_tail.
            // This 'j' serves as the witness for min(s).
            assert(min(s) == m_tail);
            assert(exists |j: int| 1 <= j < s.len() && s[j] == m_tail);
            assert(exists |i: int| 0 <= i < s.len() && s[i] == min(s));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &[i32]) -> (second_smallest: i32)
    requires 
        s.len() >= 2,
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && 
            s[i] == min(s@) && s[j] != s[i]
    ensures 
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && 
            s[i] == min(s@) && s[j] == second_smallest,
        forall|k: int| 0 <= k < s.len() && s[k] != min(s@) ==> s[k] >= second_smallest
// </vc-spec>
// <vc-code>
{
    let mut min1: i32 = s[0];
    let mut min2: i32 = s[1];

    if min2 < min1 {
        let temp = min1;
        min1 = min2;
        min2 = temp;
    }

    // Proof to establish initial invariants for the loop
    proof {
        assert(min1 <= min2);
        if s[0] <= s[1] {
            assert(min1 == s[0]);
            assert(min2 == s[1]);
        } else {
            assert(min1 == s[1]);
            assert(min2 == s[0]);
        }
        assert(s.len() >= 2);
        assert(s@[0] >= min1 && s@[1] >= min1);
        assert(exists |j: int| 0 <= j < 2 && s@[j] == min1); // min1 is either s[0] or s[1]
        
        // s[0...1] are either {s[0], s[1]} or {s[1], s[0]}
        // So any k in 0..2, s[k] >= min1 holds.
        assert(forall |k: int| 0 <= k < 2 ==> s@[k] >= min1);

        // Does min2 hold the second smallest?
        // If s[0] == s[1], then min1 == s[0] and min2 == s[0].
        // In this case, there are no elements > min1 among s[0], s[1].
        // The condition (exists |k: int| 0 <= k < i && s@[k] > min1) ==> ...
        // If s[0] != s[1], then min2 is the larger of s[0], s[1] and min2 > min1.
        // So exists k=0 or k=1 s.t. s[k] == min2 and s[k] > min1.
        // This validates the initial state relative to the second invariant.
        if s@[0] != s@[1] {
            assert(min2 > min1);
            assert(exists |k: int| 0 <= k < 2 && s@[k] == min2 && s@[k] > min1);
        } else {
            // s@[0] == s@[1]
            assert(min1 == s@[0]);
            assert(min2 == s@[0]);
            // In this case, `exists |k: int| 0 <= k < 2 && s@[k] > min1` is false.
            // So the implication `... ==> (exists |k: int| 0 <= k < 2 && s@[k] == min2 && s@[k] > min1)` is vacuously true.
        }
    }


    let n = s.len();

    let mut i: int = 2;
    while i < n
        invariant
            i <= n,
            // Invariant 1: min1 is the smallest element found so far from s[0...i-1]
            forall |k: int| 0 <= k < i ==> s@[k] >= min1,
            exists |k: int| 0 <= k < i && s@[k] == min1, // min1 is present in the seen prefix

            // Invariant 2: min2 is the smallest element greater than min1 found so far
            // If there's an element greater than min1, then min2 should be one of them and be the smallest such.
            (exists |k: int| 0 <= k < i && s@[k] > min1) ==> 
                (forall |k: int| 0 <= k < i && s@[k] > min1 ==> s@[k] >= min2),
            (exists |k: int| 0 <= k < i && s@[k] > min1) ==> 
                (exists |k: int| 0 <= k < i && s@[k] == min2 && s@[k] > min1),
            
            min2 >= min1, // min2 is always greater than or equal to min1.

            // If all elements seen so far are identical to min1, then min2 must equal min1.
            // This ensures that min2 correctly tracks the smallest element greater than min1,
            // even if no such element has been seen yet.
            (forall |k: int| 0 <= k < i ==> s@[k] == min1) ==> (min2 == min1)
    {
        let current_val = s[i];
        if current_val < min1 {
            min2 = min1;
            min1 = current_val;
        } else if current_val < min2 && current_val != min1 {
            min2 = current_val;
        }
        i = i + 1;
    }

    // Post-loop assertions and proofs
    proof {
        // Prove min1 is the overall minimum
        lemma_min_is_min_of_all_elements(s@);
        assert(forall |k: int| 0 <= k < n ==> s@[k] >= min1); // from loop invariant 1
        assert(exists |k: int| 0 <= k < n && s@[k] == min1); // from loop invariant 1
        assert(min1 == min(s@));
        
        // Prove min2 is the smallest element greater than min1 (the second smallest)
        // From invariant: If (exists |k: int| 0 <= k < n && s@[k] > min1)
        // then forall |k: int| 0 <= k < n && s@[k] > min1 ==> s@[k] >= min2
        assert(forall |k: int| 0 <= k < n && s@[k] != min(s@) ==> s@[k] >= min2);

        // From invariant: If (exists |k: int| 0 <= k < n && s@[k] > min1)
        // then exists |k: int| 0 <= k < n && s@[k] == min2 && s@[k] > min1
        // We know from precondition: exists|i, j| ... s[i] == min(s@) && s[j] != s[i]
        // Which means there is at least one element s[j] > min(s@).
        // Therefore, `(exists |k: int| 0 <= k < n && s@[k] > min1)` is true.
        // So, `(exists |k: int| 0 <= k < n && s@[k] == min2 && s@[k] > min1)` is true.
        assert(exists |k: int| 0 <= k < n && s@[k] == min2 && s@[k] != min1);
    }
    
    min2
}
// </vc-code>

fn main() {
}

}