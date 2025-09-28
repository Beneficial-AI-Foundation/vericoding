// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed compilation error by using usize for loop index instead of int */
    let mut found_diff: bool = false;
    let mut i: usize = 0;
    while i < a1.len()
        invariant
            i as int >= 0,
            i as int <= a1.len() as int,
            found_diff == !(forall|j: int| 0 <= j < i as int ==> a1@[j] == a2@[j])
        decreases a1.len() - i
    {
        if a1[i] != a2[i] {
            found_diff = true;
        }
        i += 1;
    }
    !found_diff
}
// </vc-code>

}
fn main() {}