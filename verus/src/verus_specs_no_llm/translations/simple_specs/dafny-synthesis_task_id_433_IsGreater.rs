// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsGreater(n: int, a: Vec<int>) -> (result: bool)
    requires
        a != null
    ensures
        result ==> forall i :: 0 <= i < a.len() ==> n > a.spec_index(i),
        !result ==> exists i :: 0 <= i < a.len() && n <= a.spec_index(i)
{
    return false;
}

}