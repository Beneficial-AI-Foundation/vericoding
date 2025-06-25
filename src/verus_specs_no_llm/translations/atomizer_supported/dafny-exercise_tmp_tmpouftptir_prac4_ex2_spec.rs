// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn triple(a: Vec<int>) -> bool {
    
}

fn GetTriple(a: Vec<int>) -> (index: int)
    ensures 0 <= index < a.len() - 2 or index == a.len(),
            index == a.len() <==> !triple(a),
            0 <= index < a.len() - 2 <==> triple(a),
            0 <= index < a.len() - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
}

}