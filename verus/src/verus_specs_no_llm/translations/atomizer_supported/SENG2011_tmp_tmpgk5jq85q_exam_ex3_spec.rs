// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Symmetric(a: Vec<int>) -> (flag: bool)
    ensures
        flag == true ==> forall x :: 0 <= x < a.len() ==> a.spec_index(x) == a.spec_index(a.len() - x - 1),
        flag == false ==> exists x :: 0 <= x < a.len() && a.spec_index(x) != a.spec_index(a.len() - x - 1)
{
    return false;
}

}