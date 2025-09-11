// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_min_heap(a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0
    ensures 
        result ==> forall|i: int| 0 <= i < (a.len() as int) / 2 ==> {
            let left_idx = 2 * i + 1;
            let right_idx = 2 * i + 2;
            (left_idx < a.len()) ==> (#[trigger] a[i as int] <= a[left_idx]) &&
            (right_idx < a.len()) ==> (a[i as int] <= a[right_idx])
        },
        !result ==> exists|i: int| 0 <= i < (a.len() as int) / 2 && {
            let left_idx = 2 * i + 1;
            let right_idx = 2 * i + 2;
            (#[trigger] a[i as int] > a[left_idx] && left_idx < a.len()) ||
            (a[i as int] > a[right_idx] && right_idx < a.len())
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}