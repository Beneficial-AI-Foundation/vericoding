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
spec fn sumcheck(s: &[int], i: int) -> int
    recommends 0 <= i <= s.len()
    decreases i
{
    if i == 0 { 0 }
    else { s[i as nat - 1] + sumcheck(s, i - 1) }
}

proof fn sumcheck_lemma(s: &[int], i: int)
    requires 0 <= i <= s.len()
    ensures sumcheck(s, i) == sumcheck(s, i)
    decreases i
{
    if i > 0 {
        sumcheck_lemma(s, i - 1);
    }
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
fn sum(s: &[int]) -> (a: int)
    requires s.len() > 0
    ensures a == sumcheck(s, s.len() as int)
{
    let mut total: int = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            total == sumcheck(s, i as int)
    {
        total = total + s[i];
        i = i + 1;
    }
    
    proof {
        sumcheck_lemma(s, s.len() as int);
    }
    
    total
}
// </vc-code>

fn main() {
}

}