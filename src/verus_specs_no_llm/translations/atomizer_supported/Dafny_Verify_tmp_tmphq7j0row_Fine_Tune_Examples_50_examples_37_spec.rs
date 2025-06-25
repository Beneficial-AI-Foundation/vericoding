// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main(n: int) -> x: int, m: int
    requires n > 0
    ensures (n <= 0) or (0 <= m and m < n)
{
}

}