// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn AddTupleToList(l: seq<(int, int)>, t: (int, int)) -> r: seq<(int, int)>
    ensures r.len() == l.len() + 1,
            r[r.len() - 1] == t,
            forall|i: int| 0 <= i < l.len() ==> r[i] == l[i]
{
}

}