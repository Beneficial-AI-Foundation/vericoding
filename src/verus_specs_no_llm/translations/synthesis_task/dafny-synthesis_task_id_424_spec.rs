// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn ExtractRearChars(l: Seq<String>) -> (r: Seq<char>)
    requires forall|i: int| 0 <= i < l.len() ==> l[i].len() > 0
    ensures r.len() == l.len(),
            forall|i: int| 0 <= i < l.len() ==> r[i] == l[i][l[i].len() - 1]
{
}

}