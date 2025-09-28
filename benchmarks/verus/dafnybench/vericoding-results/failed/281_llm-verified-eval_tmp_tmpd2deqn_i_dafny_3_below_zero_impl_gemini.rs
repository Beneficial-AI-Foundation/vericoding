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
/* helper modified by LLM (iteration 5): No change needed, previous proof is sound. */
proof fn sum_increment(s: Seq<int>, i: nat)
    requires i < s.len()
    ensures sum(s, (i + 1) as nat) == sum(s, i) + s[i as int]
    decreases i
{
    if i > 0 {
        sum_increment(s.subrange(1, s.len() as int), (i - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added ghost qualifiers to variables to fix compilation error. */
    let mut ghost i: nat = 0;
    let mut ghost current_sum: int = 0;
    while i < ops.len()
        invariant
            i <= ops.len(),
            current_sum == sum(ops, i),
            forall|k: nat| k <= i ==> sum(ops, k) >= 0,
        decreases ops.len() - i
    {
        proof { sum_increment(ops, i); }

        let ghost next_sum = current_sum + ops[i as int];

        if next_sum < 0 {
            assert(sum(ops, (i + 1) as nat) == next_sum);
            return true;
        }
        
        current_sum = next_sum;
        i = i + 1;
    }

    return false;
}
// </vc-code>

}
fn main() {}