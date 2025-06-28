// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HasCommonElement(a: Vec<int>, b: Vec<int>) -> (result: bool)
    requires
        a != null && b != null
    ensures
        result ==> exists i, j :: 0 <= i < a.len() && 0 <= j < b.len() && a.spec_index(i) == b.spec_index(j),
        !result ==> forall i, j :: 0 <= i < a.len() && 0 <= j < b.len() ==> a.spec_index(i) != b.spec_index(j)
{
    return false;
}

}