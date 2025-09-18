// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix indexing with nat by converting to usize */
fn array_equal_helper<T>(a1: &Vec<T>, a2: &Vec<T>, idx: nat) -> (result: bool)
    where T: PartialEq<T>,
    requires
        idx <= a1.len(),
        a1.len() == a2.len(),
        forall|i: nat| i < idx ==> a1[i as usize] == a2[i as usize],
    ensures
        result == true <==> (forall|i: nat| idx <= i < a1.len() ==> a1[i as usize] == a2[i as usize]) &&
        (idx == a1.len() ==> result == true)
{
    if idx == a1.len() as nat {
        true
    } else {
        if a1[idx as usize] == a2[idx as usize] {
            array_equal_helper(a1, a2, idx + 1)
        } else {
            false
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn array_equal<T>(a1: &Vec<T>, a2: &Vec<T>) -> (result: bool)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures 
        result == true <==> (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i]) &&
        (a1.len() == 0 ==> result == true) &&
        (exists|i: int| 0 <= i < a1.len() && !(a1[i] == a2[i]) ==> result == false)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Convert usize to nat for helper call */
{
    let len = a1.len();
    if len == 0 {
        true
    } else {
        array_equal_helper(a1, a2, 0 as nat)
    }
}
// </vc-code>

}
fn main() {}