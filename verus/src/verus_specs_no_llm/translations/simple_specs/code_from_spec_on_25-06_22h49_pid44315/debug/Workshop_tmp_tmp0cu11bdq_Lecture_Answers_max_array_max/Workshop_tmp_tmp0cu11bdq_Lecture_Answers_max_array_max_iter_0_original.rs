// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(a: Vec<int>) -> (max: int)
    requires
        a != null
    ensures
        forall j :: j >= 0 && j < a.len() ==> max >= a.spec_index(j),
        a.len() > 0 ==> exists j :: j >= 0 && j < a.len() && max == a.spec_index(j)
{
    return 0;
}

}