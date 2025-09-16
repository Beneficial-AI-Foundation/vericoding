// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fix overflow and termination issues by ensuring `mid` is always greater than `start` and `end` is always greater than `mid` for valid recursive calls. */
fn max_element_helper(a: &Vec<i32>, start: usize, end: usize) -> (max: i32)
    requires
        start < end,
        (end as int) <= a.len(),
    ensures
        forall|i: int| (start as int) <= i < (end as int) ==> a[i] <= max,
        exists|i: int| (start as int) <= i < (end as int) && a[i] == max,
    decreases end - start,
{
    if start + 1 == end {
        a[start]
    } else {
        let mid: usize = start + (end - start) / 2;

        // Proof that mid is always valid for recursive calls
        proof {
            assert((end - start) / 2 >= 0);
            assert(start + (end - start) / 2 >= start);
            assert(start + (end - start) / 2 < end);
        }

        let max1 = max_element_helper(a, start, mid);
        let max2 = max_element_helper(a, mid, end);
        if max1 >= max2 {
            max1
        } else {
            max2
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)

    requires
        a.len() > 0,

    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): No changes needed in vc-code, all fixes are in helper fn. */
{
    let len_usize = a.len();
    max_element_helper(a, 0, len_usize)
}
// </vc-code>

}
fn main() {}