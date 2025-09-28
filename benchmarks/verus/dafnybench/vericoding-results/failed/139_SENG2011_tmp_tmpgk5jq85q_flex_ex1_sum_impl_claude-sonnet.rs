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
proof fn sumcheck_lemma(s: &[int], i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures sumcheck(s, j) == sumcheck(s, i) + sumcheck(&s@.subrange(i as int, s.len() as int), j - i)
    decreases j - i
{
    if i == j {
        assert(sumcheck(s, i) == sumcheck(s, j));
        assert(sumcheck(&s@.subrange(i as int, s.len() as int), 0) == 0);
    } else {
        sumcheck_lemma(s, i, j - 1);
        assert(s@[j - 1] == s@.subrange(i as int, s.len() as int)[j - 1 - i]);
    }
}

proof fn sumcheck_extend(s: &[int], i: int)
    requires 0 < i <= s.len()
    ensures sumcheck(s, i) == sumcheck(s, i - 1) + s@[i - 1]
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn sum(s: &[int]) -> (a: int)
    requires s.len() > 0
    ensures sumcheck(s, s.len() as int) == a
// </vc-spec>
// <vc-code>
{
    let mut sum: int = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            sum == sumcheck(s, i as int)
    {
        sum = sum + s[i];
        i = i + 1;
        
        proof {
            sumcheck_extend(s, i as int);
        }
    }
    
    sum
}
// </vc-code>

fn main() {
}

}