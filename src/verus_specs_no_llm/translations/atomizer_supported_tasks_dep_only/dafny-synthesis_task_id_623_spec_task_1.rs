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

fn PowerOfListElements(l: Seq<int>, n: int) -> (result: Seq<int>)
    requires
        n >= 0
    ensures
        result.len() == l.len(),
        forall i :: 0 <= i < l.len() ==> result.spec_index(i) == Power(l.spec_index(i), n)
{
    return Seq::empty();
}

}