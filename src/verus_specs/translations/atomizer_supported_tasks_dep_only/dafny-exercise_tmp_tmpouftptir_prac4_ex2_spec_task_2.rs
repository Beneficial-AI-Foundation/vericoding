use vstd::prelude::*;

verus! {

// ATOM 
spec fn triple(a: &[int]) -> bool {
    exists|i: int| 0 <= i < a.len() - 2 && a[i] == a[i + 1] && a[i + 1] == a[i + 2]
}

// SPEC 
pub fn GetTriple(a: &[int]) -> (index: usize)
    ensures
        0 <= index < a.len() - 2 || index == a.len(),
    ensures
        index == a.len() <==> !triple(a),
    ensures
        0 <= index < a.len() - 2 <==> triple(a),
    ensures
        0 <= index < a.len() - 2 ==> a[index as int] == a[index as int + 1] && a[index as int + 1] == a[index as int + 2],
{
}

// SPEC 
pub fn TesterGetTriple() {
}

}