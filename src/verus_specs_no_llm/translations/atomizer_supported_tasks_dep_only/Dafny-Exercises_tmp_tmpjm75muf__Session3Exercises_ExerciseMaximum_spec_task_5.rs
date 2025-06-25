// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn mmaximum1(v: Vec<int>) -> (i: int)
    requires v.len()>0
    ensures 0<=i<v.len(),
            forall|k: int| 0<=k<v.len() ==> v[i]>=v[k]
{
}

}