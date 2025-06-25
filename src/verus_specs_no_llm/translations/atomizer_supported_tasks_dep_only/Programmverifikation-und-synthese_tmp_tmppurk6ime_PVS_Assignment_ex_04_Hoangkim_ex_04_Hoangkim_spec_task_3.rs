// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn intDivImpl(n: int, d: int) -> q: int, r: int
    requires n >= d and n >= 0 and d > 0;
    ensures (d*q)+r == n and 0 <= q <= n/2 and 0 <= r < d;
{
}

}