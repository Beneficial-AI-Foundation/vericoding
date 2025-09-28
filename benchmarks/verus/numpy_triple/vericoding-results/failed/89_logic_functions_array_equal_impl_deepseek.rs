// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn array_equal_helper<T: PartialEq<T>>(a1: &Vec<T>, a2: &Vec<T>, i: nat) -> (result: bool)
    requires
        i <= a1.len() as nat,
        a1.len() == a2.len(),
    ensures
        result == true <==> (forall|j: int| i <= j < a1.len() as int ==> a1@[j] == a2@[j])
{
    /* helper modified by LLM (iteration 5): Fix type mismatches and indexing */
    if i as usize >= a1.len() {
        true
    } else {
        let rest_equal = array_equal_helper(a1, a2, (i as usize + 1) as nat);
        rest_equal && a1[i as usize] == a2[i as usize]
    }
}
// </vc-helpers>

// <vc-spec>
fn array_equal<T>(a1: &Vec<T>, a2: &Vec<T>) -> (result: bool)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures 
        result == true <==> (forall|i: int| 0 <= i < a1.len() as int ==> a1@[i] == a2@[i]) &&
        (a1.len() == 0 ==> result == true) &&
        (exists|i: int| 0 <= i < a1.len() as int && !(a1@[i] == a2@[i]) ==> result == false)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Convert integer 0 to nat type */
    let result = array_equal_helper(a1, a2, 0 as nat);
    result
}
// </vc-code>

}
fn main() {}