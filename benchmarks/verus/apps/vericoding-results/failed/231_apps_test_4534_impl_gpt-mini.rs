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
proof fn binomial_nonneg(n: int, k: int)
    requires 0 <= k <= n,
    ensures
        binomial(n, k) >= 0,
    decreases n
{
    if k == 0 || k == n {
    } else {
        binomial_nonneg(n - 1, k - 1);
        binomial_nonneg(n - 1, k);
    }
}

proof fn binomial_pos(n: int, k: int)
    requires 0 <= k <= n,
    ensures
        binomial(n, k) > 0,
    decreases n
{
    if k == 0 || k == n {
    } else {
        binomial_pos(n - 1, k - 1);
        binomial_pos(n - 1, k);
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
    let mut result: Vec<u8> = Vec::new();
    let mut i: u8 = 0;
    while i <= k
        invariant
            0 <= i as int,
            i as int <= k as int + 1,
        decreases
            (k as int - i as int)
    {
        let b: int = binomial(k as int, i as int);
        proof {
            binomial_nonneg(k as int, i as int);
            binomial_pos(k as int, i as int);
        }
        result.push(b as u8);
        i = i + 1;
    }
    result
}

// </vc-code>


}

fn main() {}