// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures
        s == x+y,
        (m == x || m == y) && x <= m && y <= m
{
    return (0, 0);
}

}