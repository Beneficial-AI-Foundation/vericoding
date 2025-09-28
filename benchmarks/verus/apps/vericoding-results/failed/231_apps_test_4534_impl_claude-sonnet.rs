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
/* helper modified by LLM (iteration 5): added proof steps for bounds checking */
spec fn binomial_positive(n: int, k: int) -> bool
    recommends 0 <= k <= n
{
    binomial(n, k) > 0
}

proof fn binomial_fits_u8(n: int, k: int)
    requires 0 <= k <= n <= 33
    ensures binomial(n, k) <= 255
    decreases n
{
    if k == 0 || k == n {
        assert(binomial(n, k) == 1);
    } else if k == 1 {
        assert(binomial(n, k) == n);
        assert(n <= 33);
    } else {
        binomial_fits_u8(n-1, k-1);
        binomial_fits_u8(n-1, k);
        assert(binomial(n, k) == binomial(n-1, k-1) + binomial(n-1, k));
        assert(binomial(n-1, k-1) <= 255);
        assert(binomial(n-1, k) <= 255);
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
    /* code modified by LLM (iteration 5): fixed invariant maintenance and bounds checking */
    let mut result = Vec::new();
    
    if k == 0 {
        result.push(1);
        return result;
    }
    
    let mut prev_row = Vec::new();
    prev_row.push(1);
    
    let mut current_k = 1;
    
    while current_k <= k
        invariant
            prev_row.len() == current_k,
            forall|i: int| 0 <= i < prev_row.len() ==> #[trigger] prev_row[i] as int == binomial(current_k as int - 1, i),
            forall|i: int| 0 <= i < prev_row.len() ==> prev_row[i] > 0,
            1 <= current_k <= k + 1,
        decreases k - current_k
    {
        let mut new_row = Vec::new();
        new_row.push(1);
        
        let mut i = 1;
        while i < current_k
            invariant
                new_row.len() == i,
                new_row[0] == 1,
                forall|j: int| 1 <= j < new_row.len() ==> #[trigger] new_row[j] as int == binomial(current_k as int, j),
                forall|j: int| 0 <= j < new_row.len() ==> new_row[j] > 0,
                1 <= i <= current_k,
                prev_row.len() == current_k,
                forall|j: int| 0 <= j < prev_row.len() ==> #[trigger] prev_row[j] as int == binomial(current_k as int - 1, j),
                forall|j: int| 0 <= j < prev_row.len() ==> prev_row[j] > 0,
                1 <= current_k <= k,
            decreases current_k - i
        {
            proof {
                assert(0 <= i <= current_k - 1 <= current_k <= k <= 33);
                binomial_fits_u8(current_k as int, i as int);
            }
            let val = prev_row[(i-1) as usize] + prev_row[i as usize];
            new_row.push(val);
            i += 1;
        }
        
        new_row.push(1);
        prev_row = new_row;
        current_k += 1;
        
        proof {
            assert(prev_row.len() == current_k);
        }
    }
    
    prev_row
}
// </vc-code>


}

fn main() {}