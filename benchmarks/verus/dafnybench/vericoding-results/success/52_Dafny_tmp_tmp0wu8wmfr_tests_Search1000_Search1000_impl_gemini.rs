// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_2_pow(n: int) -> bool
    decreases n
{
    if n < 1 {
        false
    } else if n == 1 {
        true
    } else {
        n % 2 == 0 && is_2_pow(n / 2)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn search_1000(a: &[i32], x: i32) -> (k: usize)
    requires 
        a.len() >= 1000,
        forall|p: int, q: int| 0 <= p < q < 1000 ==> a[p] <= a[q],
    ensures 
        0 <= k <= 1000,
        forall|r: int| 0 <= r < k ==> a[r] < x,
        forall|r: int| k <= r < 1000 ==> a[r] >= x,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added function preconditions to loop invariants */
    let mut low: usize = 0;
    let mut high: usize = 1000;
    while low < high
        invariant
            0 <= low <= high <= 1000,
            a.len() >= 1000,
            forall|p: int, q: int| 0 <= p < q < 1000 ==> a[p] <= a[q],
            forall|i: int| 0 <= i < low ==> a[i] < x,
            forall|i: int| high <= i < 1000 ==> a[i] >= x,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if a[mid] < x {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}
// </vc-code>

}
fn main() {}