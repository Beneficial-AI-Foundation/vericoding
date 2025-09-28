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

proof fn binomial_divisible(n: int, k: int)
    requires
        0 <= k <= n,
    ensures
        binomial(n, k) > 0,
    decreases n
{
    if k == 0 || k == n {
        // Base case: binomial(n,0) = binomial(n,n) = 1 > 0
    } else if k == 1 {
        // binomial(n,1) = n > 0 when n >= 1
        assert(n > 0);
    } else {
        // Recursive case: binomial(n,k) = binomial(n-1,k-1) + binomial(n-1,k)
        // Both terms are positive by induction hypothesis
        binomial_divisible(n-1, k-1);
        binomial_divisible(n-1, k);
        assert(binomial(n-1, k-1) > 0);
        assert(binomial(n-1, k) > 0);
        assert(binomial(n,k) == binomial(n-1,k-1) + binomial(n-1,k));
    }
}

fn compute_binomial_term(k: u8, i: u8) -> (term: u8)
    requires
        i <= k,
        k <= 33,
    ensures
        term as int == binomial(k as int, i as int),
        term > 0
{
    if i == 0 {
        1u8
    } else if i == k {
        1u8
    } else if i == 1 {
        k
    } else {
        // Iterative computation
        let mut term_val: u64 = 1;
        let mut j: u8 = 1;
        while j <= i {
            invariant
                j <= i + 1,
                term_val as int == binomial(k as int, (j - 1) as int),
                term_val > 0,
            decreases i - j
        {
            term_val = term_val * ((k - j + 1) as u64) / (j as u64);
            j = j + 1;
        }
        term_val as u8
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
    /* code modified by LLM (iteration 5): fix type conversion and loop variables */
    let mut result: Vec<u8> = Vec::with_capacity((k + 1) as usize);
    
    let mut i: u8 = 0;
    while i <= k {
        invariant
            i <= k + 1,
            result.len() == i as usize,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] as int == binomial(k as int, j),
            forall|j: int| 0 <= j < result.len() ==> result[j] > 0,
        decreases k - i
        {
        let term = compute_binomial_term(k, i);
        result.push(term);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}