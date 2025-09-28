use vstd::prelude::*;

verus! {

// sums from index 0 -> i - 1
spec fn sumcheck(s: &[int], i: int) -> int
    recommends 0 <= i <= s.len()
    decreases i when 0 <= i <= s.len()
{
    if i == 0 { 0 }
    else { s[i as nat - 1] + sumcheck(s, i - 1) }
}

// returns sum of array

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn sum(s: &[int]) -> (a: int)
    requires s.len() > 0
    ensures sumcheck(s, s.len() as int) == a
// </vc-spec>
// <vc-code>
{
    proof {
        let n = s.len();
        let mut j: usize = 0;
        let mut accum: int = 0;
        while j < n
            invariant 
                0 <= j <= n,
                accum == sumcheck(s, j as int)
            decreases n - j
        {
            accum = accum + s[j];
            j += 1;
        }
        accum
    }
}
// </vc-code>

fn main() {
}

}