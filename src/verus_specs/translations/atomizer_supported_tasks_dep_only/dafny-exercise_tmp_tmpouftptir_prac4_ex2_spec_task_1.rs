use vstd::prelude::*;

verus! {

// ATOM 
spec fn triple(a: &[int]) -> bool {
    exists|i: int| 0 <= i < a.len() - 2 && a[i] == a[i + 1] && a[i + 1] == a[i + 2]
}

// SPEC 

pub fn GetTriple(a: &[int]) -> (index: int)
    ensures
        0 <= index < a.len() - 2 || index == a.len(),
    ensures
        index == a.len() <==> !triple(a),
    ensures
        0 <= index < a.len() - 2 <==> triple(a),
    ensures
        0 <= index < a.len() - 2 ==> a[index] == a[index + 1] && a[index + 1] == a[index + 2],
{
}

}