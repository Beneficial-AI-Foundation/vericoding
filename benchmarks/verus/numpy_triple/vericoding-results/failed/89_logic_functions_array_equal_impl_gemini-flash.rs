// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type casting in loop condition */
proof fn lemma_array_equal_is_reflexive<T>(a: &Vec<T>)
    where T: PartialEq<T>,
{
    assert(forall|i: int| 0 <= i && i < a.len() as int ==> a@[i] == a@[i]);
}

fn array_equal_internal<T>(a1: &Vec<T>, a2: &Vec<T>) -> (result: bool)
    where T: PartialEq<T>,
    requires a1.len() == a2.len(),
    ensures
        result == true <==> (forall|i: int| 0 <= i < a1.len() as int ==> a1@[i] == a2@[i]),
        (a1.len() == 0 ==> result == true),
        (exists|i: int| 0 <= i < a1.len() as int && !(a1@[i] == a2@[i]) ==> result == false)

{
    if a1.len() == 0 {
        return true;
    }

    let mut i: nat = 0;
    while (i as int) < (a1.len() as int)
        invariant
            0 <= i as int,
            i as int <= a1.len() as int,
            a1.len() == a2.len(),
            forall|j: int| 0 <= j && j < i as int ==> a1@[j] == a2@[j],
        decreases a1.len() as int - i as int
    {
        if a1@[i as int] != a2@[i as int] {
            return false;
        }
        i = i + 1;
    }
    true
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
/* code modified by LLM (iteration 5): Calls `array_equal_internal` */
{
    array_equal_internal(a1, a2)
}
// </vc-code>

}
fn main() {}