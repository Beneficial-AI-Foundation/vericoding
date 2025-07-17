// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_AddTupleToList(l: seq<(int, int)>, t: (int, int)) -> r: seq<(int, int)>
    ensures
        r.len() == l.len() + 1,
        r.index(r.len() - 1) == t,
        forall |i: int| 0 <= i < l.len() ==> r.index(i) == l.index(i)
;

proof fn lemma_AddTupleToList(l: seq<(int, int)>, t: (int, int)) -> (r: seq<(int, int)>)
    ensures
        r.len() == l.len() + 1,
        r.index(r.len() - 1) == t,
        forall |i: int| 0 <= i < l.len() ==> r.index(i) == l.index(i)
{
    (0, 0)
}

}