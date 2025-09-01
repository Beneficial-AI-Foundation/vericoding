use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_non_decreasing(v: &Vec<i32>) -> bool {
    if v.len() < 2 {
        true
    } else {
        for i in 0..v.len()-1 {
            assert!(i < v.len());
            assert!(i+1 < v.len());
            if v[i] > v[i+1] {
                return false;
            }
        }
        true
    }
}

fn is_non_increasing(v: &Vec<i32>) -> bool {
    if v.len() < 2 {
        true
    } else {
        for i in 0..v.len()-1 {
            assert!(i < v.len());
            assert!(i+1 < v.len());
            if v[i] < v[i+1] {
                return false;
            }
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
    is_non_decreasing(&l) || is_non_increasing(&l)
}
// </vc-code>

fn main() {}
}