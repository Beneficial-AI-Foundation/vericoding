// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &[i32]) -> (result: bool)
    requires a.len() > 0
    ensures result <==> exists|i: int| #![trigger a.spec_index(i)] 
        0 <= i < (a.len() as int) - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added trigger to the quantifier in the loop invariant */
    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            forall|j: int| #![trigger a.spec_index(j + 1)] 0 <= j < i as int ==> a.spec_index(j) + 1 != a.spec_index(j + 1),
        decreases (a.len() - 1) - i
    {
        if let Some(val) = a[i].checked_add(1) {
            if val == a[i+1] {
                return true;
            }
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}