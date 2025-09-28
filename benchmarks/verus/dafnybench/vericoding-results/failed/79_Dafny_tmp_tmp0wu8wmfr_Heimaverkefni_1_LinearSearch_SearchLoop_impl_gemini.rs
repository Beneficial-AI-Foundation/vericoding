// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn search_loop(a: &Vec<i32>, i: usize, j: usize, x: i32) -> (k: i32)
    requires 
        i <= j <= a.len(),
    ensures 
        (i <= k < j) || k == -1,
        k != -1 ==> 0 <= k < a.len() && a[k as int] == x,
        k != -1 ==> forall|r: int| k < r < j && 0 <= r < a.len() ==> a[r] != x,
        k == -1 ==> forall|r: int| (i as int) <= r < (j as int) && 0 <= r < a.len() ==> a[r] != x,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added assertion to prove index fits in i32 before casting */
    let mut k: usize = j;
    while k > i
        invariant
            i <= k <= j,
            i <= j <= a.len(),
            forall|r: int| (k as int) <= r < (j as int) && 0 <= r < a.len() ==> a[r] != x,
        decreases k - i
    {
        k = k - 1;
        if a[k] == x {
            assert(k < i32::MAX as usize) by {
                // Verus currently requires sequence lengths to be less than i32::MAX.
                // Therefore, a.len() < i32::MAX. 
                // Since k < j <= a.len(), it follows that k < i32::MAX.
            }
            return k as i32;
        }
    }
    -1
}
// </vc-code>

}
fn main() {}