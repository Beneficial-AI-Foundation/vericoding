// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn InsertBeforeEach(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures
        v.len() == 2 * s.len(),
        forall i :: 0 <= i < s.len() ==> v.spec_index(2*i) == x && v.spec_index(2*i + 1) == s.spec_index(i)
{
    return Seq::empty();
}

}