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
// Helper lemma to prove that sumcheck at position i+1 equals sumcheck at position i plus s[i]
proof fn sumcheck_step(s: &[i64], i: int)
    requires 0 <= i < s.len(),
    ensures sumcheck(s@, i + 1) == sumcheck(s@, i) + s@[i as nat] as int,
{
    // By definition of sumcheck
    assert(sumcheck(s@, i + 1) == s@[(i + 1) as nat - 1] as int + sumcheck(s@, (i + 1) - 1));
    assert((i + 1) as nat - 1 == i as nat);
    assert((i + 1) - 1 == i);
}

// Modified sumcheck to work with i64 slices
spec fn sumcheck(s: Seq<i64>, i: int) -> int
    recommends 0 <= i <= s.len()
    decreases i when 0 <= i <= s.len()
{
    if i == 0 { 0 }
    else { s[i as nat - 1] as int + sumcheck(s, i - 1) }
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
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
    invariant 
        0 <= i <= s.len(),
        sum as int == sumcheck(s@, i as int),
    {
        sum = sum + s[i];
        
        proof {
            sumcheck_step(s, i as int);
            assert(sumcheck(s@, (i + 1) as int) == sumcheck(s@, i as int) + s@[i as nat] as int);
        }
        
        i = i + 1;
    }
    
    sum
}
// </vc-code>

fn main() {
}

}