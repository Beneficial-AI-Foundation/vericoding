// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fibo(n: int) -> (result:nat)
    decreases n
{
    if n <= 0 { 0 } else if n == 1 { 1 }
    else { fibo(n - 2) + fibo(n - 1) }
}

spec fn fibo_fits_i32(n: int) -> (result:bool) {
    fibo(n) < 0x8000_0000
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn fibonacci(n: usize) -> (ret: Vec<i32>)

    requires
        fibo_fits_i32(n as int),
        n >= 2,

    ensures
        forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] ==  fibo(i), 
        ret@.len() == n,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}