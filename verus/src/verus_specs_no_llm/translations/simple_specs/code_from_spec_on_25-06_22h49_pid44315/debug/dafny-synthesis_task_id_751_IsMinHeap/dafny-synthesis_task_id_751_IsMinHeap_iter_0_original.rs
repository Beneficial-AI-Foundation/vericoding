// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsMinHeap(a: Vec<int>) -> (result: bool)
    requires
        a != null
    ensures
        result ==> forall i :: 0 <= i < a.len() / 2 ==> a.spec_index(i) <= a.spec_index(2*i + 1) && (2*i + 2 == a.len() || a.spec_index(i) <= a.spec_index(2*i + 2)),
        !result ==> exists i :: 0 <= i < a.len() / 2 && (a.spec_index(i) > a.spec_index(2*i + 1) || (2*i + 2 != a.len() && a.spec_index(i) > a.spec_index(2*i + 2)))
{
    return false;
}

}