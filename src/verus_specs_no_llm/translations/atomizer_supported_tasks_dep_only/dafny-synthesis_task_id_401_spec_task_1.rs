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

fn IndexWiseAddition(a: Seq<Seq<int>>, b: Seq<Seq<int>>) -> (result: Seq<Seq<int>>)
    requires
        a.len() > 0 && b.len() > 0,
        a.len() == b.len(),
        forall i :: 0 <= i < a.len() ==> a.spec_index(i).len() == b.spec_index(i).len()
    ensures
        result.len() == a.len(),
        forall i :: 0 <= i < result.len() ==> result.spec_index(i).len() == a.spec_index(i).len(),
        forall i :: 0 <= i < result.len() ==> forall j :: 0 <= j < result.spec_index(i).len() ==> result.spec_index(i)[j] == a.spec_index(i)[j] + b.spec_index(i)[j]
{
    return Seq::empty();
}

}