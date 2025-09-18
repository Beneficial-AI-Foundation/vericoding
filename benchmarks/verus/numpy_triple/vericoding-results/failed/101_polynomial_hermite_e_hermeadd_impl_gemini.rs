// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added cast to i32 to fix type mismatch */
spec fn spec_sum_at_index(i: int, c1: Seq<i32>, c2: Seq<i32>) -> i32 {
    let coeff1 = if i < c1.len() { c1[i] } else { 0 };
    let coeff2 = if i < c2.len() { c2[i] } else { 0 };
    (coeff1 + coeff2) as i32
}
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            let coeff1 = if i < c1.len() { c1[i] } else { 0 };
            let coeff2 = if i < c2.len() { c2[i] } else { 0 };
            #[trigger] result[i] == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): no logical changes, using fixed helper */
    let n1 = c1.len();
    let n2 = c2.len();
    let max_len = if n1 >= n2 { n1 } else { n2 };

    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < max_len
        invariant
            n1 == c1.len(),
            n2 == c2.len(),
            max_len == if n1 >= n2 { n1 } else { n2 },
            i <= max_len,
            result.len() == i,
            result.view() == Seq::new(i as nat, |j: int| spec_sum_at_index(j, c1.view(), c2.view())),
        decreases max_len - i
    {
        let coeff1 = if i < n1 { c1[i] } else { 0 };
        let coeff2 = if i < n2 { c2[i] } else { 0 };

        assert(coeff1 + coeff2 == spec_sum_at_index(i as int, c1.view(), c2.view()));

        result.push(coeff1 + coeff2);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}