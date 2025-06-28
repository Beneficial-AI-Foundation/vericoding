// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Sum(n: nat) -> (s: int)
    ensures
        s == sum(n)
{
    return 0;
}

}