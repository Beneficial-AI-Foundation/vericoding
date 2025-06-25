// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn addImp(l: List<int>) -> (r: int)
    ensures r == add(l)
{
}

}