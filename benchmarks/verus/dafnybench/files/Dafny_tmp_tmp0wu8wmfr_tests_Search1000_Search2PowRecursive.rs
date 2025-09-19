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
fn search_2_pow_recursive(a: &[i8], i: u8, n: u8, x: i8) -> (k: u8)
    requires
        i as int + n as int <= a@.len(),
        ({(forall|p: int, q: int|
            0 <= p < q && i as int <= p && q < (i as int + n as int) ==> 
            a@[p] <= a@[q])}),
        is_2_pow((n as int + 1) as int),
    ensures
        i as int <= k as int <= i as int + n as int,
        ({(forall|r: int|
            0 <= r && i as int <= r < k as int ==> 
            a@[r] < x as int)}),
        ({(forall|r: int|
            0 <= r && k as int <= r < (i as int + n as int) ==> 
            a@[r] >= x as int)}),
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