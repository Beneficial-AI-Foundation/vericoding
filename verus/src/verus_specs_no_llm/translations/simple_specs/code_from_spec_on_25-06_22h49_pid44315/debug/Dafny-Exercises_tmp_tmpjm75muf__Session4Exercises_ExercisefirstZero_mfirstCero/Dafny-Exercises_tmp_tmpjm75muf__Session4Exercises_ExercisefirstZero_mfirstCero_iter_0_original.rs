// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mfirstCero(v: Vec<int>) -> (i: int)
    ensures
        0 <=i<=v.len(),
        forall j:: 0<=j<i ==> v.spec_index(j)!=0,
        i!=v.len() ==> v.spec_index(i)==0
{
    return 0;
}

}