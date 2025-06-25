// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AddTupleToList(l: seq<(int, int)>, t: (int, int)) -> (r: seq<(int, int)>)
    ensures
        r.len() == l.len() + 1,
        r.spec_index(r.len() - 1) == t,
        forall i :: 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index(i)
{
    return (0, 0);
}

}