// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HasOnlyOneDistinctElement(a: Vec<int>) -> (result: bool)
    requires
        a != null
    ensures
        result ==> forall i, j :: 0 <= i < a.len() && 0 <= j < a.len() ==> a.spec_index(i) == a.spec_index(j),
        !result ==> exists i, j :: 0 <= i < a.len() && 0 <= j < a.len() && a.spec_index(i) != a.spec_index(j)
{
    return false;
}

}