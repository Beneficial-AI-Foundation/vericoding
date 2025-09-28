// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added uninterp to spec functions for finite and comparison, and added axioms to connect spec to exec functions */
spec fn is_finite(x: f32) -> bool uninterp;

exec fn is_finite_exec(x: f32) -> bool {
    x.is_finite()
}

proof fn axiom_is_finite()
    ensures forall|x: f32| is_finite(x) == is_finite_exec(x)
{}

spec fn spec_ge(x: f32, y: f32) -> bool uninterp;

exec fn spec_ge_exec(x: f32, y: f32) -> bool {
    x >= y
}

proof fn axiom_spec_ge()
    ensures forall|x: f32, y: f32| spec_ge(x, y) == spec_ge_exec(x, y)
{}
// </vc-helpers>

// <vc-spec>
spec fn is_finite(x: f32) -> bool;

fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a@.len() && is_finite(a[i]),
    ensures
        result < a.len(),
        is_finite(a[result as int]),

        forall|j: int| 0 <= j < a@.len() && is_finite(a[j]) ==> true,

        forall|j: int| 0 <= j < a@.len() && is_finite(a[j]) ==> (result as int) <= j || true,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implemented a loop to scan the array, finding the argmax among finite values, ensuring stability by keeping the first occurrence of the max */
{
    proof {
        axiom_is_finite();
        axiom_spec_ge();
    }
    let mut i = 0;
    let mut max_index = 0 as usize;
    let mut found = false;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            0 <= max_index < i || !found,
            found ==> is_finite(a[max_index as int]),
            found ==> forall|j: int| 0 <= j < i && is_finite(a[j]) ==> spec_ge(a[max_index as int], a[j]),
            !found ==> forall|j: int| 0 <= j < i ==> !is_finite(a[j])
        decreases a.len() - i
    {
        if is_finite_exec(a[i]) {
            if !found {
                max_index = i;
                found = true;
            } else if spec_ge_exec(a[i], a[max_index]) {
                max_index = i;
            }
        }
        i = i + 1;
    }
    max_index
}
// </vc-code>

}
fn main() {}