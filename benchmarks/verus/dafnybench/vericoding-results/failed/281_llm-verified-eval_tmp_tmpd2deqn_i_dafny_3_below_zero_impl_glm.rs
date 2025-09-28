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

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    proof {
        let mut current_sum = 0;
        let mut i: nat = 0;
        while i < ops.len()
            invariant
                0 <= i <= ops.len(),
                current_sum == sum(ops, i),
        {
            current_sum += ops[i as int];
            if current_sum < 0 {
                return true;
            }
            i += 1;
        }
        false
    }
}
// </vc-code>

fn main() {
}

}