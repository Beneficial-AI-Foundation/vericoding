// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn binomial(n: int, k: int) -> int
    decreases n when 0 <= k <= n
{
    if k == 0 || k == n { 1 }
    else if k == 1 { n }
    else { binomial(n-1, k-1) + binomial(n-1, k) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unnecessary decreases clause */
proof fn lemma_sum_into_vec(k_v: int, i_v: int, a: u8, b: u8)
    requires
        0 <= i_v,
        i_v <= k_v,
        k_v > 0,
        a as int == binomial(k_v - 1, i_v - 1),
        b as int == binomial(k_v - 1, i_v),
        binomial(k_v, i_v) == binomial(k_v - 1, i_v - 1) + binomial(k_v - 1, i_v)
    ensures
        (a + b) as int == binomial(k_v, i_v)
{
    // No proof steps needed, as the ensures clause directly uses the requires clause for simplification
}
// </vc-helpers>

// <vc-spec>
fn get_row(k: u8) -> (result: Vec<u8>)
    requires k <= 33
    ensures 
        result.len() == k + 1,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] as int == binomial(k as int, i),
        forall|i: int| 0 <= i < result.len() ==> result[i] > 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed decreases clause from recursive call */
{
    if k == 0 {
        let mut result = Vec::new();
        result.push(1);
        result
    } else {
        let prev_row = get_row(k - 1);
        let mut result = Vec::new();
        result.push(1);

        let mut i: u8 = 1;
        while i < k
            invariant
                1 <= i,
                i <= k,
                result.len() == i as nat,
                forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] as int == binomial(k as int, j),
                prev_row.len() == (k - 1) as nat + 1,
                forall|j: int| 0 <= j < prev_row.len() ==> #[trigger] prev_row[j] as int == binomial((k - 1) as int, j),
            decreases k - i
        {
            let a = prev_row[(i - 1) as usize];
            let b = prev_row[i as usize];
            let sum = a + b;
            result.push(sum);

            proof {
                let k_v = k as int;
                let i_v = i as int;
                lemma_sum_into_vec(k_v, i_v, a, b);
            }
            i = i + 1;
        }
        result.push(1);
        result
    }
}
// </vc-code>


}

fn main() {}