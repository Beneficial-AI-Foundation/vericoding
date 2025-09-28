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
/* code modified by LLM (iteration 4): Fixed compilation error by removing unused helper function */
{
    let mut current_row: Vec<u8> = Vec::new();
    current_row.push(1);
    let mut i: u8 = 1;
    while i <= k
        invariant
            current_row.len() == i as usize,
            forall|j: int| 0 <= j < current_row.len() as int ==> current_row[j] as int == binomial(i as int - 1, j),
            forall|j: int| 0 <= j < current_row.len() as int ==> current_row[j] > 0,
            i <= k + 1,
        decreases (k - i) as nat
    {
        let mut next_row: Vec<u8> = Vec::new();
        next_row.push(1);
        let mut j: u8 = 1;
        while j < i
            invariant
                next_row.len() == j as usize,
                forall|p: int| 0 <= p < next_row.len() as int ==> next_row[p] as int == binomial(i as int, p),
                forall|p: int| 0 <= p < next_row.len() as int ==> next_row[p] > 0,
                j <= i,
            decreases (i - j) as nat
        {
            let prev_val1 = current_row[(j-1) as usize];
            let prev_val2 = current_row[j as usize];
            let next_val = prev_val1 + prev_val2;
            next_row.push(next_val);
            j = j + 1;
        }
        next_row.push(1);
        current_row = next_row;
        i = i + 1;
    }
    current_row
}
// </vc-code>


}

fn main() {}