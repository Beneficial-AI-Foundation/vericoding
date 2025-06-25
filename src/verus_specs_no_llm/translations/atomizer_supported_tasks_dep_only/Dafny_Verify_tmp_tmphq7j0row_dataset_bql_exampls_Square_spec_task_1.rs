// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn square(n: int) -> (r: int)
    requires 0 <= n;
    ensures r == n*n;
{
}

}