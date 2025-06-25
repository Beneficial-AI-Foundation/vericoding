// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IndexWiseAddition(a: Seq<Seq<int>>, b: Seq<Seq<int>>) -> (result: Seq<Seq<int>>)
    requires a.len() > 0 and b.len() > 0,
             a.len() == b.len(),
             forall|i: int| 0 <= i < a.len() ==> a[i].len() == b[i].len()
    ensures result.len() == a.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i].len() == a[i].len(),
            forall|i: int| 0 <= i < result.len() ==> forall|j: int| 0 <= j < result[i].len() ==> result[i][j] == a[i][j] + b[i][j]
{
}

}