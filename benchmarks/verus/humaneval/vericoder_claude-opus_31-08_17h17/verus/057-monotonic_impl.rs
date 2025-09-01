use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemmas for monotonic verification
proof fn lemma_monotonic_increasing_step(l: Seq<i32>, i: int)
    requires
        0 < i < l.len(),
        forall|a: int, b: int| 0 <= a < b < i ==> l[a] <= l[b],
        l[i - 1] <= l[i],
    ensures
        forall|a: int, b: int| 0 <= a < b <= i ==> l[a] <= l[b],
{
    assert forall|a: int, b: int| 0 <= a < b <= i implies l[a] <= l[b] by {
        if b < i {
            // Already known from precondition
            assert(l[a] <= l[b]);
        } else if b == i {
            if a == i - 1 {
                // Direct comparison
                assert(l[a] <= l[b]);
            } else {
                // a < i - 1, so a < i - 1 < i
                assert(l[a] <= l[i - 1]);  // by precondition with a, i-1
                assert(l[i - 1] <= l[i]);   // by precondition
                assert(l[a] <= l[i]);       // transitivity
            }
        }
    }
}

proof fn lemma_monotonic_decreasing_step(l: Seq<i32>, i: int)
    requires
        0 < i < l.len(),
        forall|a: int, b: int| 0 <= a < b < i ==> l[a] >= l[b],
        l[i - 1] >= l[i],
    ensures
        forall|a: int, b: int| 0 <= a < b <= i ==> l[a] >= l[b],
{
    assert forall|a: int, b: int| 0 <= a < b <= i implies l[a] >= l[b] by {
        if b < i {
            // Already known from precondition
            assert(l[a] >= l[b]);
        } else if b == i {
            if a == i - 1 {
                // Direct comparison
                assert(l[a] >= l[b]);
            } else {
                // a < i - 1, so a < i - 1 < i
                assert(l[a] >= l[i - 1]);  // by precondition with a, i-1
                assert(l[i - 1] >= l[i]);   // by precondition
                assert(l[a] >= l[i]);       // transitivity
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn monotonic(l: Vec<i32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if l.len() <= 1 {
        return true;
    }
    
    let mut increasing = true;
    let mut decreasing = true;
    let mut i: usize = 1;
    
    while i < l.len()
        invariant
            1 <= i <= l.len(),
            increasing ==> (forall|a: int, b: int| 0 <= a < b < i ==> l@[a] <= l@[b]),
            decreasing ==> (forall|a: int, b: int| 0 <= a < b < i ==> l@[a] >= l@[b]),
            !increasing && !decreasing ==> (
                exists|a: int, b: int| 0 <= a < b <= i && #[trigger] l@[a] > l@[b]
            ) && (
                exists|a: int, b: int| 0 <= a < b <= i && #[trigger] l@[a] < l@[b]
            ),
        decreases l.len() - i,
    {
        let old_increasing = increasing;
        let old_decreasing = decreasing;
        
        if l[i - 1] > l[i] {
            increasing = false;
            if old_decreasing {
                // We just found a decreasing pair
                assert(l@[i - 1] > l@[i]);
                assert(0 <= (i - 1) as int && ((i - 1) as int) < i as int && i as int <= i as int);
            }
        } else if increasing {
            proof {
                lemma_monotonic_increasing_step(l@, i as int);
            }
        }
        
        if l[i - 1] < l[i] {
            decreasing = false;
            if old_increasing {
                // We just found an increasing pair
                assert(l@[i - 1] < l@[i]);
                assert(0 <= (i - 1) as int && ((i - 1) as int) < i as int && i as int <= i as int);
            }
        } else if decreasing {
            proof {
                lemma_monotonic_decreasing_step(l@, i as int);
            }
        }
        
        // Maintain the invariant for the !increasing && !decreasing case
        if !increasing && !decreasing {
            if old_increasing && !increasing {
                // Just turned increasing to false, so we found l[i-1] > l[i]
                assert(exists|a: int, b: int| 0 <= a < b <= i as int + 1 && l@[a] > l@[b]) by {
                    assert(l@[(i - 1) as int] > l@[i as int]);
                }
            }
            if old_decreasing && !decreasing {
                // Just turned decreasing to false, so we found l[i-1] < l[i]
                assert(exists|a: int, b: int| 0 <= a < b <= i as int + 1 && l@[a] < l@[b]) by {
                    assert(l@[(i - 1) as int] < l@[i as int]);
                }
            }
            // If already !increasing && !decreasing, the witnesses still exist in range [0, i+1]
        }
        
        i = i + 1;
    }
    
    assert(i == l.len());
    
    if increasing {
        assert forall|a: int, b: int| 0 <= a < b < l@.len() implies l@[a] <= l@[b] by {
            assert(l@[a] <= l@[b]);
        }
    }
    
    if decreasing {
        assert forall|a: int, b: int| 0 <= a < b < l@.len() implies l@[a] >= l@[b] by {
            assert(l@[a] >= l@[b]);
        }
    }
    
    increasing || decreasing
}
// </vc-code>

fn main() {}
}