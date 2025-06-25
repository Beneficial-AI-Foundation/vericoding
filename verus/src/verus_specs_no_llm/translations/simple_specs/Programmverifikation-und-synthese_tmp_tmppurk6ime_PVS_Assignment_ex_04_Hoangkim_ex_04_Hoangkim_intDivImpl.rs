// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn intDivImpl(n: int, d: int) -> (q: int, r: int)
    requires
        n >= d && n >= 0 && d > 0
    ensures
        (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d
{
    return (0, 0);
}

}