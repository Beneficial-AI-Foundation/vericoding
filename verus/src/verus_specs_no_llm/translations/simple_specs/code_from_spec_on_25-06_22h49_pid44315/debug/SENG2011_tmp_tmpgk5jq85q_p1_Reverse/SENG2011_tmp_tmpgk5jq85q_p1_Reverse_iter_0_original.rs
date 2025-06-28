// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<char>) -> (b: Vec<char>)
    requires
        a.len() > 0
    ensures
        a.len() == b.len(),
        forall x :: 0 <= x < a.len() ==> b.spec_index(x) == a.spec_index(a.len() - x - 1)
{
    return Vec::new();
}

}