use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    if l@.len() <= 1nat {
        return true;
    }
    
    let mut is_non_decreasing = true;
    let mut is_non_increasing = true;
    
    for i in 0..(l.len() - 1)
        invariant
            0 <= i <= l@.len() - 1,
            is_non_decreasing <==> (forall|k: int, m: int| 0 <= k < m < i + 1 ==> l@.index(k) <= l@.index(m)),
            is_non_increasing <==> (forall|k: int, m: int| 0 <= k < m < i + 1 ==> l@.index(k) >= l@.index(m)),
    {
        if l[i] > l[i + 1] {
            is_non_decreasing = false;
        }
        if l[i] < l[i + 1] {
            is_non_increasing = false;
        }
        
        assert(forall|k: int, m: int| 0 <= k < m < i + 2 ==> 
            if m == i + 1 {
                if is_non_decreasing { l@.index(k) <= l@.index(m) } else { true }
            } else {
                if is_non_decreasing { l@.index(k) <= l@.index(m) } else { true }
            });
            
        assert(forall|k: int, m: int| 0 <= k < m < i + 2 ==> 
            if m == i + 1 {
                if is_non_increasing { l@.index(k) >= l@.index(m) } else { true }
            } else {
                if is_non_increasing { l@.index(k) >= l@.index(m) } else { true }
            });
    }
    
    is_non_decreasing || is_non_increasing
}
// </vc-code>

fn main() {}
}