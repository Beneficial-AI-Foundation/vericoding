use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemmas for monotonic verification
proof fn lemma_monotonic_increasing_transitive(l: Seq<i32>, i: int, j: int, k: int)
    requires
        0 <= i < j < k < l.len(),
        forall|a: int, b: int| 0 <= a < b < l.len() && b <= j ==> l[a] <= l[b],
        l[j] <= l[k],
    ensures
        forall|a: int, b: int| 0 <= a < b < l.len() && b <= k ==> l[a] <= l[b],
{
    assert forall|a: int, b: int| 0 <= a < b < l.len() && b <= k implies l[a] <= l[b] by {
        if b <= j {
            assert(l[a] <= l[b]);
        } else if b == k {
            if a < j {
                assert(l[a] <= l[j]);
                assert(l[j] <= l[k]);
            } else {
                assert(a == j);
                assert(l[a] <= l[b]);
            }
        }
    }
}

proof fn lemma_monotonic_decreasing_transitive(l: Seq<i32>, i: int, j: int, k: int)
    requires
        0 <= i < j < k < l.len(),
        forall|a: int, b: int| 0 <= a < b < l.len() && b <= j ==> l[a] >= l[b],
        l[j] >= l[k],
    ensures
        forall|a: int, b: int| 0 <= a < b < l.len() && b <= k ==> l[a] >= l[b],
{
    assert forall|a: int, b: int| 0 <= a < b < l.len() && b <= k implies l[a] >= l[b] by {
        if b <= j {
            assert(l[a] >= l[b]);
        } else if b == k {
            if a < j {
                assert(l[a] >= l[j]);
                assert(l[j] >= l[k]);
            } else {
                assert(a == j);
                assert(l[a] >= l[b]);
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
            increasing ==> (forall|a: int, b: int| 0 <= a < b < l.len() && b < i ==> l@[a] <= l@[b]),
            decreasing ==> (forall|a: int, b: int| 0 <= a < b < l.len() && b < i ==> l@[a] >= l@[b]),
        decreases l.len() - i,
    {
        if increasing && l[i - 1] > l[i] {
            increasing = false;
        }
        
        if decreasing && l[i - 1] < l[i] {
            decreasing = false;
        }
        
        if increasing {
            proof {
                lemma_monotonic_increasing_transitive(l@, 0, (i - 1) as int, i as int);
            }
        }
        
        if decreasing {
            proof {
                lemma_monotonic_decreasing_transitive(l@, 0, (i - 1) as int, i as int);
            }
        }
        
        i = i + 1;
    }
    
    increasing || decreasing
}
// </vc-code>

fn main() {}
}