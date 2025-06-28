use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q[i] <= q[j]
}

// Helper function to check if a sequence is sorted (executable version)
fn is_sorted(q: &Vec<i32>) -> (result: bool)
    ensures result == Sorted(q@.map(|_idx, x: i32| x as int))
{
    let ghost seq_int = q@.map(|_idx, x: i32| x as int);
    
    if q.len() <= 1 {
        proof {
            if q.len() == 0 {
                assert(seq_int.len() == 0);
                assert(forall|i: int, j: int| 0 <= i <= j < seq_int.len() ==> seq_int[i] <= seq_int[j]) by {
                    // Vacuously true for empty sequence
                }
            } else {
                assert(seq_int.len() == 1);
                assert(forall|i: int, j: int| 0 <= i <= j < seq_int.len() ==> seq_int[i] <= seq_int[j]) by {
                    // Only case is i=j=0
                }
            }
        }
        return true;
    }
    
    let mut i: usize = 0;
    while i < q.len() - 1
        invariant 
            0 <= i <= q.len() - 1,
            q.len() >= 2,
            seq_int == q@.map(|_idx, x: i32| x as int),
            forall|k: int| 0 <= k < i ==> seq_int[k] <= seq_int[k + 1],
            forall|k: int, l: int| 0 <= k <= l <= i ==> seq_int[k] <= seq_int[l]
    {
        if q[i] > q[i + 1] {
            proof {
                assert(seq_int[i as int] == q[i] as int);
                assert(seq_int[i as int + 1] == q[i + 1] as int);
                assert(seq_int[i as int] > seq_int[i as int + 1]);
                assert(0 <= i as int <= i as int + 1 < seq_int.len());
                assert(!Sorted(seq_int));
            }
            return false;
        }
        
        proof {
            // Prove the stronger invariant for the next iteration
            assert(forall|k: int, l: int| 0 <= k <= l <= i + 1 ==> seq_int[k] <= seq_int[l]) by {
                assert forall|k: int, l: int| 0 <= k <= l <= i + 1 implies seq_int[k] <= seq_int[l] by {
                    if l <= i {
                        // This case is covered by the existing invariant
                    } else {
                        // l == i + 1
                        assert(l == i + 1);
                        if k == l {
                            // trivial case
                        } else if k == i {
                            // We just checked that seq_int[i] <= seq_int[i + 1]
                            assert(seq_int[k] <= seq_int[l]);
                        } else {
                            // k < i, so we can use transitivity
                            assert(k <= i);
                            assert(seq_int[k] <= seq_int[i]); // from invariant
                            assert(seq_int[i] <= seq_int[i + 1]); // just checked
                            assert(seq_int[k] <= seq_int[l]);
                        }
                    }
                }
            }
        }
        
        i += 1;
    }
    
    // Prove that the sequence is sorted
    proof {
        assert(i == q.len() - 1);
        assert(forall|k: int, l: int| 0 <= k <= l <= q.len() - 1 ==> seq_int[k] <= seq_int[l]);
        
        assert(forall|k: int, l: int| 0 <= k <= l < seq_int.len() ==> seq_int[k] <= seq_int[l]) by {
            assert forall|k: int, l: int| 0 <= k <= l < seq_int.len() implies seq_int[k] <= seq_int[l] by {
                assert(l < seq_int.len());
                assert(l <= seq_int.len() - 1);
                assert(l <= q.len() - 1);
                // This follows from our loop invariant
            }
        }
    }
    
    true
}

// Helper lemma to prove transitivity in sorted sequences
proof fn sorted_transitivity_lemma(q: Seq<int>, start: int, end: int)
    requires 
        0 <= start < end < q.len(),
        forall|i: int| 0 <= i < q.len() - 1 ==> q[i] <= q[i + 1]
    ensures q[start] <= q[end]
    decreases end - start
{
    if start + 1 == end {
        // Base case: adjacent elements
        assert(q[start] <= q[end]);
    } else {
        // Recursive case: use transitivity
        sorted_transitivity_lemma(q, start, end - 1);
        assert(q[start] <= q[end - 1]);
        assert(q[end - 1] <= q[end]);
        assert(q[start] <= q[end]);
    }
}

// Proof function demonstrating properties of sorted sequences
proof fn sorted_empty_and_single()
    ensures Sorted(Seq::<int>::empty())
    ensures forall|x: int| Sorted(seq![x])
{
    // Empty sequence is trivially sorted
    let empty_seq = Seq::<int>::empty();
    assert(empty_seq.len() == 0);
    assert(forall|i: int, j: int| 0 <= i <= j < empty_seq.len() ==> empty_seq[i] <= empty_seq[j]) by {
        // Vacuously true since there are no valid i, j
    }
    
    // Single element sequence is sorted
    assert(forall|x: int| Sorted(seq![x])) by {
        assert forall|x: int| Sorted(seq![x]) by {
            let single_seq = seq![x];
            assert(single_seq.len() == 1);
            assert(forall|i: int, j: int| 0 <= i <= j < single_seq.len() ==> single_seq[i] <= single_seq[j]) by {
                assert forall|i: int, j: int| 0 <= i <= j < single_seq.len() implies single_seq[i] <= single_seq[j] by {
                    // Only valid case is i = j = 0
                    assert(0 <= i <= j < 1);
                    assert(i == 0 && j == 0);
                    assert(single_seq[i] == x && single_seq[j] == x);
                }
            }
        }
    }
}

// Proof function showing that subsequences of sorted sequences are sorted
proof fn sorted_subsequence(q: Seq<int>, start: int, end: int)
    requires Sorted(q)
    requires 0 <= start <= end <= q.len()
    ensures Sorted(q.subrange(start, end))
{
    let sub = q.subrange(start, end);
    
    assert(forall|i: int, j: int| 0 <= i <= j < sub.len() ==> sub[i] <= sub[j]) by {
        assert forall|i: int, j: int| 0 <= i <= j < sub.len() implies sub[i] <= sub[j] by {
            // sub[i] corresponds to q[start + i] and sub[j] corresponds to q[start + j]
            assert(sub[i] == q[start + i]);
            assert(sub[j] == q[start + j]);
            assert(0 <= start + i <= start + j < start + sub.len());
            assert(start + sub.len() == end);
            assert(start + j < end);
            assert(start + i <= start + j < q.len());
            // Since q is sorted, we have q[start + i] <= q[start + j]
        }
    }
}

}