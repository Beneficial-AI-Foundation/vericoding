use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn AddTupleToList(l: seq<(int, int)>, t: (int, int)) -> seq<(int, int)>
    ensures
        AddTupleToList(l, t).len() == l.len() + 1,
        AddTupleToList(l, t).spec_index(AddTupleToList(l, t).len() - 1) == t,
        forall|i: int| 0 <= i < l.len() ==> AddTupleToList(l, t).spec_index(i) == l.spec_index(i)
{
    l.push(t)
}

}