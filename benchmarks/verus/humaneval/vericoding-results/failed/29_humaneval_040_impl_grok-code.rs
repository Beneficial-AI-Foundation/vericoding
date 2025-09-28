// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_triple_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int, k: int| 0 <= i < j < k < l.len() && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn triples_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_triple_sum_to_zero(l@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Added invariants for loop bounds and used i64 casts for sum */
    let n = l.len();
    if n < 3 {
        return false;
    }
    for i in 0..n
        invariant
            n == l.len(),
    {
        for j in (i + 1)..n
            invariant
                n == l.len(),
        {
            for k in (j + 1)..n
                invariant
                    n == l.len(),
            {
                let i_val = l[i] as i64;
                let j_val = l[j] as i64;
                let k_val = l[k] as i64;
                if i_val + j_val + k_val == 0 {
                    return true;
                }
            }
        }
    }
    false
}
// </vc-code>


}

fn main() {}