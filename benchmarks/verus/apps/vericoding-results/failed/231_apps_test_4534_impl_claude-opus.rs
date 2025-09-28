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
{
    /* code modified by LLM (iteration 5): Fixed initialization and loop invariants for correct binomial calculation */
    let mut row = Vec::new();
    row.push(1u8);
    
    if k == 0 {
        return row;
    }
    
    let mut i = 1u8;
    while i <= k
        invariant
            i >= 1,
            i <= k + 1,
            row.len() == i as int,
            forall|j: int| 0 <= j < row.len() ==> #[trigger] row[j] as int == binomial((i - 1) as int, j),
            forall|j: int| 0 <= j < row.len() ==> row[j] > 0,
        decreases (k - i) as int
    {
        // Create new row from previous row
        let mut new_row = Vec::new();
        new_row.push(1u8);
        
        let mut j = 1u8;
        while j < i
            invariant
                j >= 1,
                j <= i,
                new_row.len() == j as int,
                row.len() == i as int,
                forall|m: int| 0 <= m < new_row.len() ==> #[trigger] new_row[m] as int == binomial(i as int, m),
                forall|m: int| 0 <= m < row.len() ==> #[trigger] row[m] as int == binomial((i - 1) as int, m),
                forall|m: int| 0 <= m < new_row.len() ==> new_row[m] > 0,
                forall|m: int| 0 <= m < row.len() ==> row[m] > 0,
            decreases (i - j) as int
        {
            let val1 = row[(j - 1) as usize];
            let val2 = row[j as usize];
            
            proof {
                assert(binomial(i as int, j as int) == binomial((i - 1) as int, (j - 1) as int) + binomial((i - 1) as int, j as int));
                assert(val1 as int == binomial((i - 1) as int, (j - 1) as int));
                assert(val2 as int == binomial((i - 1) as int, j as int));
            }
            
            new_row.push((val1 + val2) as u8);
            j = j + 1;
        }
        
        new_row.push(1u8);
        row = new_row;
        i = i + 1;
    }
    
    row
}
// </vc-code>


}

fn main() {}