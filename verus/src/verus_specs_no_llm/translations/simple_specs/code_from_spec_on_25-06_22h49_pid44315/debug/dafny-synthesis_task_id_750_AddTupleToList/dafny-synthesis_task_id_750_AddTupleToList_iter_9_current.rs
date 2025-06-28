use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn AddTupleToList(l: seq<(int, int)>, t: (int, int)) -> seq<(int, int)>
    ensures
        |r: seq<(int, int)>| r.len() == l.len() + 1,
        |r: seq<(int, int)>| r.spec_index(r.len() - 1) == t,
        |r: seq<(int, int)>| forall|i: int| 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index(i)
{
    l.push(t)
}

}