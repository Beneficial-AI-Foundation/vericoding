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
proof fn sumcheck_step(s: &[int], i: int)
    requires
        0 <= i < s.len() as int,
    ensures
        sumcheck(s, i as int) + s[i as nat] == sumcheck(s, (i + 1) as int),
{
    reveal(sumcheck);
}

lemma sumcheck_base(s: &[int])
    ensures
        sumcheck(s, 0) == 0,
{
    reveal(sumcheck);
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
    let mut a: int = 0;
    let mut i: usize = 0;
    let n = s.len();
    assert(n > 0);
    proof {
        sumcheck_base(s);
    }
    
    while i < n
        invariant
            0 <= i <= n,
            a == sumcheck(s, i as int),
        decreases n - i,
    {
        let old_i = i;
        a = a + s[i];
        i = i + 1;
        proof {
            sumcheck_step(s, old_i as int);
        }
    }
    
    a
}
// </vc-code>

fn main() {
}

}