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
proof fn sumcheck_step(s: &[int], i: usize)
    requires
        i < s.len()
    ensures
        sumcheck(s, i as int + 1) == s[i as nat] + sumcheck(s, i as int)
{
    let k: int = i as int + 1;

    assert(0 <= k && k <= s.len() as int);
    assert(k != 0);

    assert(sumcheck(s, k) == if k == 0 { 0 } else { s[k as nat - 1] + sumcheck(s, k - 1) });

    assert(k - 1 == i as int);
    assert((k as nat) - 1 == i as nat);
    assert(s[(k as nat) - 1] == s[i as nat]);

    assert(sumcheck(s, k) == s[i as nat] + sumcheck(s, i as int));
    assert(sumcheck(s, i as int + 1) == s[i as nat] + sumcheck(s, i as int));
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
    let mut i: usize = 0;
    let ghost mut acc: int = 0int;

    assert(sumcheck(s, 0int) == 0int);

    while i < s.len()
        invariant
            0 <= i as int
            && i <= s.len()
            && i as int <= s.len() as int
            && acc == sumcheck(s, i as int)
    {
        let old_i = i;

        proof {
            acc = s[old_i as nat] + acc;
        }

        i = i + 1;

        proof {
            sumcheck_step(s, old_i);
            assert(acc == sumcheck(s, old_i as int + 1));
            assert(old_i + 1 == i);
            assert(acc == sumcheck(s, i as int));
        }
    }

    assert(i == s.len());
    assert(acc == sumcheck(s, s.len() as int));
    acc
}
// </vc-code>

fn main() {
}

}