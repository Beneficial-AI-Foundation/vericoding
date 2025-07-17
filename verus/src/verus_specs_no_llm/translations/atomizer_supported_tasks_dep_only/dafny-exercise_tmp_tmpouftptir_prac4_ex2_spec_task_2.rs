// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn triple(a: Vec<int>) -> bool {
    
}

spec fn spec_GetTriple(a: Vec<int>) -> index: int
    ensures
        0 <= index < a.len() - 2 || index == a.len(),
        index == a.len() <==> !triple(a),
        0 <= index < a.len() - 2 <==> triple(a),
        0 <= index < a.len() - 2 ==> a.index(index) == a.index(index + 1) == a.index(index + 2)
;

proof fn lemma_GetTriple(a: Vec<int>) -> (index: int)
    ensures
        0 <= index < a.len() - 2 || index == a.len(),
        index == a.len() <==> !triple(a),
        0 <= index < a.len() - 2 <==> triple(a),
        0 <= index < a.len() - 2 ==> a.index(index) == a.index(index + 1) == a.index(index + 2)
{
    0
}

}