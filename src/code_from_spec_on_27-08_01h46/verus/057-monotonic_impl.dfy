use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_non_decreasing(l: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < l.len() ==> l.index(i) <= l.index(j)
}

spec fn is_non_increasing(l: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < l.len() ==> l.index(i) >= l.index(j)
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
    if l@.len() <= 1 {
        return true;
    }
    
    let mut non_decreasing = true;
    let mut non_increasing = true;
    
    for i in 0..l.len() - 1
        invariant
            0 <= i <= l@.len() - 1,
            non_decreasing ==> (forall|k: int, m: int| 0 <= k < m < i + 1 ==> l@.index(k) <= l@.index(m)),
            non_increasing ==> (forall|k: int, m: int| 0 <= k < m < i + 1 ==> l@.index(k) >= l@.index(m)),
    {
        if l[i] > l[i + 1] {
            non_decreasing = false;
        }
        if l[i] < l[i + 1] {
            non_increasing = false;
        }
        if !non_decreasing && !non_increasing {
            return false;
        }
    }
    
    proof {
        if non_decreasing {
            assert(forall|k: int, m: int| 0 <= k < m < l@.len() ==> l@.index(k) <= l@.index(m));
        }
        if non_increasing {
            assert(forall|k: int, m: int| 0 <= k < m < l@.len() ==> l@.index(k) >= l@.index(m));
        }
    }
    
    true
}
// </vc-code>

}
fn main() {}