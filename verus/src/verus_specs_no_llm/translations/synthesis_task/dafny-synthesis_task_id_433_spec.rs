// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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