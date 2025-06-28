// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Min(x: int, y: int) -> (m: int)
    ensures
        m <= x && m <= y,
        m == x || m == y
{
    return 0;
}

}