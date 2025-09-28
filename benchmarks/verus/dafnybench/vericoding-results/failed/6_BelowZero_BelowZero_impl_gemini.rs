// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>, n: nat) -> int
    recommends n <= s.len()
    decreases n
{
    if s.len() == 0 || n == 0 {
        0
    } else {
        s[0] + sum(s.subrange(1, s.len() as int), (n - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Add proof for base case i=0 */
proof fn sum_lemma(s: Seq<int>, i: nat)
    requires
        i < s.len(),
    ensures
        sum(s, (i + 1) as nat) == sum(s, i) + s[i as int],
    decreases i
{
    if i > 0 {
        sum_lemma(s.subrange(1, s.len() as int), (i - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): The function must be a 'proof' function to operate on ghost types; the body is a proof block returning a bool. */
{
    let result = proof {
        let mut current_sum: int = 0;
        let mut i: nat = 0;
        let mut found = false;
        while i < ops.len()
            invariant
                i <= ops.len(),
                current_sum == sum(ops, i),
                found <==> (exists|k: nat| 1 <= k && k <= i && sum(ops, k) < 0),
            decreases ops.len() - i
        {
            if !found {
                sum_lemma(ops, i);
                let new_sum = current_sum + ops[i as int];
                if new_sum < 0 {
                    assert(sum(ops, (i + 1) as nat) == new_sum) by {
                        // Proved by sum_lemma
                    };
                    found = true;
                }
                current_sum = new_sum;
            }
            i = i + 1;
        }
        if found {
            assert(exists|n: nat| n <= ops.len() && sum(ops, n) < 0);
        } else {
            assert(forall|k: nat| k <= i ==> sum(ops, k) >= 0);
            assert(!(exists|n: nat| n <= ops.len() && sum(ops, n) < 0));
        }
        found
    };
    result
}
// </vc-code>

}
fn main() {}