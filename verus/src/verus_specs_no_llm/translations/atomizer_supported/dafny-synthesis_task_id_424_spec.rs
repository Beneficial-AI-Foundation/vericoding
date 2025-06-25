// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ExtractRearChars(l: Seq<String>) -> (r: Seq<char>)
    requires
        forall i :: 0 <= i < l.len() ==> l.spec_index(i).len() > 0
    ensures
        r.len() == l.len(),
        forall i :: 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index(i)[l.spec_index(i).len() - 1]
{
    return Seq::empty();
}

}