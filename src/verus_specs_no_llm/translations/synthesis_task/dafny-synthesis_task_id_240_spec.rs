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

fn ReplaceLastElement(first: Seq<int>, second: Seq<int>) -> (result: Seq<int>)
    requires
        first.len() > 0
    ensures
        result.len() == first.len() - 1 + second.len(),
        forall i :: 0 <= i < first.len() - 1 ==> result.spec_index(i) == first.spec_index(i),
        forall i :: first.len() - 1 <= i < result.len() ==> result.spec_index(i) == second.spec_index(i - first.len() + 1)
{
    return Seq::empty();
}

}