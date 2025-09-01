use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn is_monotonic_increasing(l: Seq<i32>) -> (b: bool)
    ensures
        b <==> forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] <= l[j]
{
    if l.len() == 0 {
        true
    } else {
        let mut i: int = 0;
        while i < l.len() - 1
            invariant
                0 <= i <= l.len() - 1,
                forall|k: int, m: int| 0 <= k < m <= i ==> l[k] <= l[m],
        {
            if l[i] > l[i+1] {
                return false;
            }
            i = i + 1;
        }
        true
    }
}

proof fn is_monotonic_decreasing(l: Seq<i32>) -> (b: bool)
    ensures
        b <==> forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] >= l[j]
{
    if l.len() == 0 {
        true
    } else {
        let mut i: int = 0;
        while i < l.len() - 1
            invariant
                0 <= i <= l.len() - 1,
                forall|k: int, m: int| 0 <= k < m <= i ==> l[k] >= l[m],
        {
            if l[i] < l[i+1] {
                return false;
            }
            i = i + 1;
        }
        true
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
    if l.len() == 0 {
        true
    } else {
        let mut increasing = true;
        let mut decreasing = true;
        let mut i: usize = 0;
        
        while i < l.len() - 1
            invariant
                0 <= i <= l.len() - 1,
                increasing ==> forall|k: int, m: int| 0 <= k < m <= i as int ==> l@[k] <= l@[m],
                decreasing ==> forall|k: int, m: int| 0 <= k < m <= i as int ==> l@[k] >= l@[m],
                increasing || decreasing,
        {
            if l[i] < l[i+1] {
                decreasing = false;
            } else if l[i] > l[i+1] {
                increasing = false;
            }
            
            if !increasing && !decreasing {
                break;
            }
            
            i = i + 1;
        }
        
        proof {
            if increasing {
                assert(is_monotonic_increasing(l@));
                assert(forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j));
            } else if decreasing {
                assert(is_monotonic_decreasing(l@));
                assert(forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j));
            }
        }
        
        increasing || decreasing
    }
}
// </vc-code>

fn main() {}
}