// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn aba(a: Vec<int>) -> (b: Vec<int>)
    ensures
        a.len() == b.len() // needed for next line,
        forall x :: 0<=x<b.len() ==> b.spec_index(x) == abs(a.spec_index(x))
{
    return Vec::new();
}

}