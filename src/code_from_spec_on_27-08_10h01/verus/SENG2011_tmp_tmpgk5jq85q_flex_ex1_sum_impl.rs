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
proof fn lemma_sumcheck_append(s: &[int], i: int)
    requires 0 <= i < s.len()
    ensures sumcheck(s, i + 1) == s[i] + sumcheck(s, i)
{
}

proof fn lemma_sumcheck_monotonic(s: &[int], i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures sumcheck(s, j) == sumcheck(s, i) + sumcheck(s@.subrange(i, j), (j - i) as int)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn sum(s: &[int]) -> (a: int)
    requires s.len() > 0
    ensures sumcheck(s, s.len() as int) == a
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result: int = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            result == sumcheck(s, i as int)
    {
        result = result + s[i];
        i += 1;
        
        proof {
            lemma_sumcheck_append(s, (i - 1) as int);
        }
    }
    
    result
}
// </vc-code>

fn main() {
}

}