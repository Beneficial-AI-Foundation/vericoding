// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn mfirstCero(v: Vec<int>) -> (i: int)
    ensures 0 <=i<=v.len(),
            forall|j: int| 0<=j<i ==> v[j]!=0,
            i!=v.len() ==> v[i]==0
{
}

}