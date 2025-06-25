// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn max(a: Vec<int>) -> (max: int)
    requires a != null;
    ensures forall|j: int| j >= 0 and j < a.len() ==> max >= a[j]; //max is larger then anything in the array,
            a.len() > 0 ==> exists|j: int| j >= 0 and j < a.len() and max == a[j]; //max is an element in the array
{
}

}