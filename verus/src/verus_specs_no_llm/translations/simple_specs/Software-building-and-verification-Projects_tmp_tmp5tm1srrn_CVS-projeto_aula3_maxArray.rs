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

fn maxArray(arr: Vec<int>) -> (max: int)
    requires
        arr.len() > 0
    ensures
        forall i: int :: 0 <= i < arr.len() ==> arr.spec_index(i) <= max,
        exists x::0 <= x < arr.len() && arr.spec_index(x) == max
{
    return 0;
}

}