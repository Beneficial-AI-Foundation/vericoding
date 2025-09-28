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
proof fn lemma_binomial_is_positive(n: int, k: int)
    requires 0 <= k <= n
    ensures binomial(n, k) > 0
    decreases n
{
    if k > 0 && k < n && n > 0 {
        lemma_binomial_is_positive(n - 1, k - 1);
        lemma_binomial_is_positive(n - 1, k);
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
{
    /* code modified by LLM (iteration 2): added decreases clauses to loops */
    let mut row = vec![1u8];
    let mut n: u8 = 0;
    while n < k
        invariant
            n <= k,
            row.len() == (n as int) + 1,
            forall|i: int| 0 <= i < row.len() ==> #[trigger] row[i] as int == binomial(n as int, i),
            forall|i: int| 0 <= i < row.len() ==> row[i] > 0,
            forall|i: int| 0 <= i <= (n as int) ==> binomial(n as int, i) <= 255,
        decreases k - n
    {
        let mut next_row = Vec::new();
        next_row.push(1u8);

        let mut i: usize = 0;
        while i < (n as usize)
            invariant
                n < k,
                row.len() == (n as int) + 1,
                forall|j: int| 0 <= j < row.len() ==> #[trigger] row[j] as int == binomial(n as int, j),
                forall|j: int| 0 <= j <= n ==> binomial(n as int, j) <= 255,

                i <= n as usize,
                next_row.len() == (i as int) + 1,
                forall|j: int| 0 <= j < next_row.len() ==> next_row[j] as int == binomial(n as int + 1, j),
                forall|j: int| 0 <= j < next_row.len() ==> next_row[j] > 0,
            decreases (n as usize) - i
        {
            let val = row[i] + row[i+1];
            proof {
                lemma_binomial_is_positive(n as int, i as int);
                lemma_binomial_is_positive(n as int, i as int + 1);
            }
            next_row.push(val);
            i = i + 1;
        }

        next_row.push(1u8);
        
        row = next_row;
        n = n + 1;
    }
    row
}
// </vc-code>


}

fn main() {}