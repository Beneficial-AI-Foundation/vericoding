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
    ensures result == Sorted(q@)
{
    if q.len() <= 1 {
        return true;
    }
    
    let mut i = 0;
    while i < q.len() - 1
        invariant 
            0 <= i <= q.len() - 1,
            forall|k: int| 0 <= k < i ==> q@[k] <= q@[k + 1]
    {
        if q[i] > q[i + 1] {
            assert(!Sorted(q@)) by {
                assert(q@[i] > q@[i + 1]);
                assert(0 <= i <= i + 1 < q@.len());
            }
            return false;
        }
        i += 1;
    }
    
    // Prove that the sequence is sorted using transitivity
    assert(Sorted(q@)) by {
        assert(forall|k: int, l: int| 0 <= k <= l < q@.len() ==> q@[k] <= q@[l]) by {
            assert forall|k: int, l: int| 0 <= k <= l < q@.len() implies q@[k] <= q@[l] by {
                if k == l {
                    // trivially true: q@[k] <= q@[k]
                } else {
                    // k < l, use transitivity through adjacent pairs
                    // We know that for all adjacent pairs, q@[i] <= q@[i+1]
                    // This gives us transitivity for the entire range
                    assert(k < l);
                    sorted_transitivity_lemma(q@, k, l);
                }
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
    assert(Sorted(Seq::<int>::empty())) by {
        let empty_seq = Seq::<int>::empty();
        assert(empty_seq.len() == 0);
        assert(forall|i: int, j: int| 0 <= i <= j < empty_seq.len() ==> empty_seq[i] <= empty_seq[j]) by {
            assert forall|i: int, j: int| 0 <= i <= j < empty_seq.len() implies empty_seq[i] <= empty_seq[j] by {
                // This is vacuously true since there are no valid i, j
            }
        }
    }
    
    // Single element sequence is sorted
    assert(forall|x: int| Sorted(seq![x])) by {
        assert forall|x: int| Sorted(seq![x]) by {
            let single_seq = seq![x];
            assert(single_seq.len() == 1);
            assert(forall|i: int, j: int| 0 <= i <= j < single_seq.len() ==> single_seq[i] <= single_seq[j]) by {
                assert forall|i: int, j: int| 0 <= i <= j < single_seq.len() implies single_seq[i] <= single_seq[j] by {
                    // Only valid case is i = j = 0, which gives x <= x (true)
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
    
    assert(Sorted(sub)) by {
        assert(forall|i: int, j: int| 0 <= i <= j < sub.len() ==> sub[i] <= sub[j]) by {
            assert forall|i: int, j: int| 0 <= i <= j < sub.len() implies sub[i] <= sub[j] by {
                // sub[i] corresponds to q[start + i] and sub[j] corresponds to q[start + j]
                assert(sub[i] == q[start + i]);
                assert(sub[j] == q[start + j]);
                assert(0 <= start + i <= start + j < start + sub.len());
                assert(start + sub.len() == end);
                assert(start + j < end);
                assert(start + i <= start + j < q.len());
                // Since q is sorted and start + i <= start + j, we have q[start + i] <= q[start + j]
                assert(q[start + i] <= q[start + j]);
            }
        }
    }
}

}