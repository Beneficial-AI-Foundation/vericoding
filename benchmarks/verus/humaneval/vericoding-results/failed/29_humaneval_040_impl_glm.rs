// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_triple_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int, k: int| 0 <= i < j < k < l.len() && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>
{
    /* code modified by LLM (iteration 5): moved int conversions to ghost code within proof block */
    let n = l.len();
    for i in 0..n
        invariant 0 <= i <= n
        decreases n - i
    {
        for j in i+1..n
            invariant i < j <= n
            decreases n - j
        {
            for k in j+1..n
                invariant j < k <= n
                decreases n - k
            {
                assert(i < n);
                assert(j < n);
                assert(k < n);
                proof {
                    let x = l[i] as int;
                    let y = l[j] as int;
                    let z = l[k] as int;
                    if x + y + z == 0 {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}
// </vc-helpers>

// <vc-spec>
fn triples_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_triple_sum_to_zero(l@.map(|i, x: i8| x as int))
// </vc-spec>
// <vc-code>

// </vc-code>


}

fn main() {}