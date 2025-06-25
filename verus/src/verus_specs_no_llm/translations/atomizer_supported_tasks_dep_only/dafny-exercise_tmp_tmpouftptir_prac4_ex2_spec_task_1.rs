// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn GetTriple(a: Vec<int>) -> (index: int)
    ensures
        0 <= index < a.len() - 2 || index == a.len(),
        index == a.len() <==> !triple(a),
        0 <= index < a.len() - 2 <==> triple(a),
        0 <= index < a.len() - 2 ==> a.spec_index(index) == a.spec_index(index + 1) == a.spec_index(index + 2)
{
    return 0;
}

}