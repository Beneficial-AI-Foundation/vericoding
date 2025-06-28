use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_seq(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

spec fn sorted_slice(a: &Vec<int>, start: int, end: int) -> bool
    requires 0 <= start <= end <= a.len()
{
    forall |i: int, j: int| start <= i < j < end ==> a[i] <= a[j]
}

// Helper spec function to check if all elements of one sequence appear in another
spec fn seq_contains_all(container: Seq<int>, contained: Seq<int>) -> bool {
    forall |i: int| 0 <= i < contained.len() ==> container.contains(contained[i])
}

// Helper lemma for subrange sortedness
proof fn lemma_subrange_sorted(a: Seq<int>, start: int, end: int)
    requires
        sorted_seq(a),
        0 <= start <= end <= a.len()
    ensures
        sorted_seq(a.subrange(start, end))
{
    let sub = a.subrange(start, end);
    assert forall |i: int, j: int| 0 <= i < j < sub.len() implies sub[i] <= sub[j] by {
        assert(sub[i] == a[start + i]);
        assert(sub[j] == a[start + j]);
        assert(start + i < start + j);
        assert(a[start + i] <= a[start + j]);
    }
}

// Helper lemma for proving element containment in subranges
proof fn lemma_subrange_contains(a: Seq<int>, start: int, end: int, x: int)
    requires
        0 <= start <= end <= a.len(),
        a.subrange(start, end).contains(x)
    ensures
        a.contains(x)
{
}

// Helper lemma for proving element containment preservation
proof fn lemma_contains_preservation(a1: Seq<int>, a2: Seq<int>, i1: int, i2: int, result: Seq<int>)
    requires
        0 <= i1 <= a1.len(),
        0 <= i2 <= a2.len(),
        seq_contains_all(result, a1.subrange(i1, a1.len() as int)),
        seq_contains_all(result, a2.subrange(i2, a2.len() as int))
    ensures
        forall |x: int| (a1.subrange(i1, a1.len() as int).contains(x) || 
                        a2.subrange(i2, a2.len() as int).contains(x)) ==> result.contains(x)
{
}

// Implementation of mergeSimple - merges two sorted sequences
fn mergeSimple(a1: Seq<int>, a2: Seq<int>) -> (result: Seq<int>)
    requires 
        sorted_seq(a1),
        sorted_seq(a2)
    ensures 
        sorted_seq(result),
        result.len() == a1.len() + a2.len(),
        // All elements from a1 and a2 appear in result
        forall |x: int| a1.contains(x) || a2.contains(x) ==> result.contains(x),
        seq_contains_all(result, a1),
        seq_contains_all(result, a2)
{
    let result = merge_recursive(a1, a2, 0, 0);
    
    proof {
        // Prove that the result contains all elements from a1 and a2
        assert(a1.subrange(0, a1.len() as int) == a1);
        assert(a2.subrange(0, a2.len() as int) == a2);
        
        assert forall |x: int| a1.contains(x) implies result.contains(x) by {
            assert(a1.subrange(0, a1.len() as int).contains(x));
        }
        
        assert forall |x: int| a2.contains(x) implies result.contains(x) by {
            assert(a2.subrange(0, a2.len() as int).contains(x));
        }
    }
    
    result
}

fn merge_recursive(a1: Seq<int>, a2: Seq<int>, i1: int, i2: int) -> (result: Seq<int>)
    requires
        sorted_seq(a1),
        sorted_seq(a2),
        0 <= i1 <= a1.len(),
        0 <= i2 <= a2.len()
    ensures
        sorted_seq(result),
        result.len() == (a1.len() - i1) + (a2.len() - i2),
        // Elements preservation
        forall |x: int| (a1.subrange(i1, a1.len() as int).contains(x) || 
                        a2.subrange(i2, a2.len() as int).contains(x)) ==> result.contains(x),
        seq_contains_all(result, a1.subrange(i1, a1.len() as int)),
        seq_contains_all(result, a2.subrange(i2, a2.len() as int))
    decreases a1.len() - i1 + a2.len() - i2
{
    if i1 >= a1.len() {
        // Take remaining elements from a2
        let remaining = a2.subrange(i2, a2.len() as int);
        proof {
            lemma_subrange_sorted(a2, i2, a2.len() as int);
            
            // Prove element containment properties
            assert forall |x: int| (a1.subrange(i1, a1.len() as int).contains(x) || 
                            a2.subrange(i2, a2.len() as int).contains(x)) implies remaining.contains(x) by {
                if a1.subrange(i1, a1.len() as int).contains(x) {
                    assert(a1.subrange(i1, a1.len() as int).len() == 0);
                    assert(false);
                }
            }
            
            assert forall |k: int| 0 <= k < a1.subrange(i1, a1.len() as int).len() implies remaining.contains(a1.subrange(i1, a1.len() as int)[k]) by {
                assert(a1.subrange(i1, a1.len() as int).len() == 0);
            }
        }
        remaining
    } else if i2 >= a2.len() {
        // Take remaining elements from a1
        let remaining = a1.subrange(i1, a1.len() as int);
        proof {
            lemma_subrange_sorted(a1, i1, a1.len() as int);
            
            // Prove element containment properties
            assert forall |x: int| (a1.subrange(i1, a1.len() as int).contains(x) || 
                            a2.subrange(i2, a2.len() as int).contains(x)) implies remaining.contains(x) by {
                if a2.subrange(i2, a2.len() as int).contains(x) {
                    assert(a2.subrange(i2, a2.len() as int).len() == 0);
                    assert(false);
                }
            }
            
            assert forall |k: int| 0 <= k < a2.subrange(i2, a2.len() as int).len() implies remaining.contains(a2.subrange(i2, a2.len() as int)[k]) by {
                assert(a2.subrange(i2, a2.len() as int).len() == 0);
            }
        }
        remaining
    } else if a1[i1] <= a2[i2] {
        // Take from a1
        let rest = merge_recursive(a1, a2, i1 + 1, i2);
        let result = seq![a1[i1]] + rest;
        
        proof {
            // Prove sortedness
            if rest.len() > 0 {
                // Prove that a1[i1] <= rest[0]
                assert forall |x: int| (a1.subrange(i1 + 1, a1.len() as int).contains(x) || 
                                a2.subrange(i2, a2.len() as int).contains(x)) implies rest.contains(x) by {
                    // This follows from the postcondition of the recursive call
                }
                
                // The first element of rest comes from either a1[i1+1..] or a2[i2..]
                // In either case, a1[i1] <= rest[0] due to sortedness
                if a1.subrange(i1 + 1, a1.len() as int).len() > 0 {
                    assert(a1[i1] <= a1[i1 + 1]); // from sorted_seq(a1)
                }
                if a2.subrange(i2, a2.len() as int).len() > 0 {
                    assert(a1[i1] <= a2[i2]); // from the condition
                }
            }
            
            assert forall |k: int, l: int| 0 <= k < l < result.len() implies result[k] <= result[l] by {
                if k == 0 && l > 0 {
                    assert(result[k] == a1[i1]);
                    assert(result[l] == rest[l - 1]);
                    if rest.len() > 0 {
                        // Use transitivity: a1[i1] <= rest[0] <= rest[l-1]
                        assert(rest[0] <= rest[l - 1]); // from sorted_seq(rest)
                    }
                } else if k > 0 && l > 0 {
                    assert(result[k] == rest[k - 1]);
                    assert(result[l] == rest[l - 1]);
                    assert(rest[k - 1] <= rest[l - 1]); // from sorted_seq(rest)
                }
            }
            
            // Prove element containment
            assert forall |x: int| (a1.subrange(i1, a1.len() as int).contains(x) || 
                            a2.subrange(i2, a2.len() as int).contains(x)) implies result.contains(x) by {
                if a1.subrange(i1, a1.len() as int).contains(x) {
                    if x == a1[i1] {
                        assert(result.contains(x));
                    } else {
                        assert(a1.subrange(i1 + 1, a1.len() as int).contains(x));
                        assert(rest.contains(x));
                        assert(result.contains(x));
                    }
                } else if a2.subrange(i2, a2.len() as int).contains(x) {
                    assert(rest.contains(x));
                    assert(result.contains(x));
                }
            }
            
            // Prove seq_contains_all for a1 subrange
            assert forall |k: int| 0 <= k < a1.subrange(i1, a1.len() as int).len() implies result.contains(a1.subrange(i1, a1.len() as int)[k]) by {
                let x = a1.subrange(i1, a1.len() as int)[k];
                if k == 0 {
                    assert(x == a1[i1]);
                    assert(result[0] == a1[i1]);
                } else {
                    assert(a1.subrange(i1 + 1, a1.len() as int)[k - 1] == x);
                    assert(rest.contains(x));
                }
            }
            
            // Prove seq_contains_all for a2 subrange
            assert forall |k: int| 0 <= k < a2.subrange(i2, a2.len() as int).len() implies result.contains(a2.subrange(i2, a2.len() as int)[k]) by {
                let x = a2.subrange(i2, a2.len() as int)[k];
                assert(rest.contains(x));
            }
        }
        
        result
    } else {
        // Take from a2
        let rest = merge_recursive(a1, a2, i1, i2 + 1);
        let result = seq![a2[i2]] + rest;
        
        proof {
            // Prove sortedness
            if rest.len() > 0 {
                // Prove that a2[i2] <= rest[0]
                // The first element of rest comes from either a1[i1..] or a2[i2+1..]
                if a1.subrange(i1, a1.len() as int).len() > 0 {
                    assert(a2[i2] < a1[i1]); // from the negation of the condition
                }
                if a2.subrange(i2 + 1, a2.len() as int).len() > 0 {
                    assert(a2[i2] <= a2[i2 + 1]); // from sorted_seq(a2)
                }
            }
            
            assert forall |k: int, l: int| 0 <= k < l < result.len() implies result[k] <= result[l] by {
                if k == 0 && l > 0 {
                    assert(result[k] == a2[i2]);
                    assert(result[l] == rest[l - 1]);
                    if rest.len() > 0 {
                        assert(rest[0] <= rest[l - 1]); // from sorted_seq(rest)
                    }
                } else if k > 0 && l > 0 {
                    assert(result[k] == rest[k - 1]);
                    assert(result[l] == rest[l - 1]);
                    assert(rest[k - 1] <= rest[l - 1]); // from sorted_seq(rest)
                }
            }
            
            // Prove element containment
            assert forall |x: int| (a1.subrange(i1, a1.len() as int).contains(x) || 
                            a2.subrange(i2, a2.len() as int).contains(x)) implies result.contains(x) by {
                if a1.subrange(i1, a1.len() as int).contains(x) {
                    assert(rest.contains(x));
                    assert(result.contains(x));
                } else if a2.subrange(i2, a2.len() as int).contains(x) {
                    if x == a2[i2] {
                        assert(result.contains(x));
                    } else {
                        assert(a2.subrange(i2 + 1, a2.len() as int).contains(x));
                        assert(rest.contains(x));
                        assert(result.contains(x));
                    }
                }
            }
            
            // Prove seq_contains_all for a1 subrange
            assert forall |k: int| 0 <= k < a1.subrange(i1, a1.len() as int).len() implies result.contains(a1.subrange(i1, a1.len() as int)[k]) by {
                let x = a1.subrange(i1, a1.len() as int)[k];
                assert(rest.contains(x));
            }
            
            // Prove seq_contains_all for a2 subrange
            assert forall |k: int| 0 <= k < a2.subrange(i2, a2.len() as int).len() implies result.contains(a2.subrange(i2, a2.len() as int)[k]) by {
                let x = a2.subrange(i2, a2.len() as int)[k];
                if k == 0 {
                    assert(x == a2[i2]);
                    assert(result[0] == a2[i2]);
                } else {
                    assert(a2.subrange(i2 + 1, a2.len() as int)[k - 1] == x);
                    assert(rest.contains(x));
                }
            }
        }
        
        result
    }
}

}