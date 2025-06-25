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

fn max(a: Vec<int>) -> (max: int)
    requires
        a != null
    ensures
        forall j :: j >= 0 && j < a.len() ==> max >= a.spec_index(j); //max is larger then anything in the array,
        a.len() > 0 ==> exists j :: j >= 0 && j < a.len() && max == a.spec_index(j); //max is an element in the array
{
    return 0;
}

}