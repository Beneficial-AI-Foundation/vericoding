// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TetrahedralNumber(n: int) -> (t: int)
    requires
        n >= 0
    ensures
        t == n * (n + 1) * (n + 2) / 6
{
    return 0;
}

}