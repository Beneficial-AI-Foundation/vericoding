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

spec fn allEqual(s: Seq<int>) -> bool {
    forall i,j::0<=i<s.len() && 0<=j<s.len() ==> s.spec_index(i)==s.spec_index(j)
}

fn mallEqual1(v: Vec<int>) -> (b: bool)
    ensures
        b==allEqual(v.spec_index(0..v.len()))
{
    return false;
}

}