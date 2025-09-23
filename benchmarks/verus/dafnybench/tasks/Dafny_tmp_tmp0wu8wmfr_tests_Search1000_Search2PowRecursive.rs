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
fn search_2_pow_recursive(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    requires
        i + n <= a.len(),
        ({(forall|p: int, q: int|
            0 <= p < q && i as int <= p && q < (i + n) as int ==> 
            a[p] <= a[q])}),
        is_2_pow((n + 1) as int),
    ensures
        i <= k <= i + n,
        ({(forall|r: int|
            0 <= r && i as int <= r < k as int ==> 
            a[r] < x)}),
        ({(forall|r: int|
            0 <= r && k as int <= r < (i + n) as int ==> 
            a[r] >= x)}),
    decreases n
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}