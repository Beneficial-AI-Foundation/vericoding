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

spec fn positive(s: Seq<int>) -> bool {
    forall u::0<=u<s.len() ==> s.spec_index(u)>=0
}

fn mpositive4(v: Vec<int>) -> (b: bool)
    ensures
        b==positive(v.spec_index(0..v.len()))
{
    return false;
}

}