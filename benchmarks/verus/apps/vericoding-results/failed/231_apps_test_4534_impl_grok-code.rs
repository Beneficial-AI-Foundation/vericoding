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
fn binomial_exec(n: int, k: int) -> int
    requires
        0 <= k <= n,
    ensures
        result == binomial(n, k),
    decreases n when 0 <= k <= n,
{
    if k == 0 || k == n {
        1
    } else if k == 1 {
        n
    } else {
        binomial_exec(n - 1, k - 1) + binomial_exec(n - 1, k)
    }
}

/* helper modified by LLM (iteration 3): exec version of binomial spec function */
proof fn lemma_binomial_exec_equals_spec(n: int, k: int)
    requires
        0 <= k <= n,
    ensures
        binomial_exec(n, k) == binomial(n, k),
    decreases n when 0 <= k <= n,
{
    if k == 0 || k == n {
    } else if k == 1 {
    } else {
        lemma_binomial_exec_equals_spec(n - 1, k - 1);
        lemma_binomial_exec_equals_spec(n - 1, k);
    }
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
/* code modified by LLM (iteration 3): compute the row of Pascal's triangle using exec binomial function */
{
    let mut result = Vec::new();
    for i in 0..=((k as usize)) {
        let b = binomial_exec(k as int, i as int);
        proof {
            lemma_binomial_exec_equals_spec(k as int, i as int);
        }
        result.push(b as u8);
    }
    result
}
// </vc-code>


}

fn main() {}