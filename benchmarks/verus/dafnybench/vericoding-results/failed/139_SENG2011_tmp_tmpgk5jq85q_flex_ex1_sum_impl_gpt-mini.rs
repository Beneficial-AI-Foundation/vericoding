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
proof fn lemma_sumcheck_snoc(s: &[int], i: nat)
    requires i < s.len()
    ensures sumcheck(s, (i as int) + 1) == sumcheck(s, i as int) + s[i]
{
    // by definition of sumcheck for positive second arg
    assert(sumcheck(s, (i as int) + 1) == s[(((i as int) + 1) as nat) - 1] + sumcheck(s, i as int));
    // arithmetic on casts: (((i as int)+1) as nat) - 1 == i
    assert((((i as int) + 1) as nat) - 1 == i);
    assert(sumcheck(s, (i as int) + 1) == s[i] + sumcheck(s, i as int));
}

fn sum_rec(s: &[int], i: nat, acc: int) -> int
    requires i <= s.len()
    requires acc == sumcheck(s, i as int)
    decreases s.len() - i
    ensures result == sumcheck(s, s.len() as int)
{
    if i == s.len() {
        acc
    } else {
        let x: int = s[i];
        let acc2: int = acc + x;
        proof {
            // show acc2 == sumcheck(s, (i as int) + 1) to satisfy recursive precondition
            lemma_sumcheck_snoc(s, i);
            assert(acc2 == sumcheck(s, (i as int) + 1));
        }
        sum_rec(s, i + 1, acc2)
    }
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
    proof {
        // sumcheck(s, 0) == 0 by definition
        assert(sumcheck(s, 0) == 0);
    }
    sum_rec(s, 0, 0)
}
// </vc-code>

fn main() {
}

}