// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ElementWiseModulo(a: Vec<int>, b: Vec<int>) -> (result: Vec<int>)
    requires
        a != null && b != null,
        a.len() == b.len(),
        forall i :: 0 <= i < b.len() ==> b.spec_index(i) != 0
    ensures
        result != null,
        result.len() == a.len(),
        forall i :: 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) % b.spec_index(i)
{
    return Vec::new();
}

}