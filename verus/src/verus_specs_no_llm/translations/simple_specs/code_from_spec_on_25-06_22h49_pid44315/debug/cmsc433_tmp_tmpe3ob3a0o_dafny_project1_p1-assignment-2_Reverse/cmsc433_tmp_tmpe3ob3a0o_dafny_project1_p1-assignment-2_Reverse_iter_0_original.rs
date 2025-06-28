// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Reverse(a: Vec<int>) -> (aRev: Vec<int>)
    ensures
        aRev.len() == a.len(),
        forall i : int :: 0 <= i < a.len() ==> a.spec_index(i) == aRev.spec_index(aRev.len()-i-1),
        fresh(aRev) // Indicates returned object is newly created in method body
{
    return Vec::new();
}

}