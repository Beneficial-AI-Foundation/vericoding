// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn pairwise_addition(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() % 2 == 0,
    ensures
        result.len() == a.len() / 2,
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == a[2*i] + a[2*i + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added explicit forall assertion to prove invariant maintenance, which fails due to unprovable absence of overflow */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len() / 2
        invariant
            a.len() % 2 == 0,
            i <= a.len() / 2,
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> 
                (result@[k] as int) == (a@[2 * k] as int) + (a@[2 * k + 1] as int),
        decreases a.len() / 2 - i
    {
        let ghost old_result = result@;
        let val1 = a[2 * i];
        let val2 = a[2 * i + 1];
        
        let sum = val1 + val2;

        result.push(sum);

        assert forall|k: int| 0 <= k < (i as int) + 1 implies
            (result@[k] as int) == (a@[2 * k] as int) + (a@[2 * k + 1] as int) by {
            if k < i as int {
                assert(result@[k] == old_result@[k]);
            } else {
                assert(k == i as int);
                assert((sum as int) == (val1 as int) + (val2 as int));
            }
        }

        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}