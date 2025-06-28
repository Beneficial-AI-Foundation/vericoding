// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn GetFirstElements(lst: Seq<Seq<int>>) -> (result: Seq<int>)
    requires
        forall i :: 0 <= i < lst.len() ==> lst.spec_index(i).len() > 0
    ensures
        result.len() == lst.len(),
        forall i :: 0 <= i < result.len() ==> result.spec_index(i) == lst.spec_index(i)[0]
{
    return Seq::empty();
}

}