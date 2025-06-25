// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main(x: int, y: int) -> x_out: int, y_out: int, n: int
    requires x >= 0,
             y >= 0,
             x == y
    ensures y_out == n
{
}

}