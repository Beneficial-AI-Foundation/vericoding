// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn GetFirstElements(lst: Seq<Seq<int>>) -> (result: Seq<int>)
    requires forall|i: int| 0 <= i < lst.len() ==> lst[i].len() > 0
    ensures result.len() == lst.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i] == lst[i][0]
{
}

}