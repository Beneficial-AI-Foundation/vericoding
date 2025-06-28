// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn sum(s: Vec<int>) -> (a: int)
    requires
        s.len() > 0
    ensures
        sumcheck(s, s.len()) == a
{
    return 0;
}

}