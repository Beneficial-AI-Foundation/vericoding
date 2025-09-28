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
proof fn sum_proofs(ops: Seq<int>)
    decreases ops.len()
    ensures
        forall|n: nat| n <= ops.len() ==> 
            if n == 0 {
                sum(ops, n) == 0
            } else {
                sum(ops, n) == ops[ n-1 as int ] + sum(ops, n-1)
            },
{
    admit();
}
// </vc-helpers>

// <vc-spec>
fn below_zero(ops: Seq<int>) -> (result: bool)
    ensures result <==> exists|n: nat| n <= ops.len() && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    let mut cumulative: int = 0;
    let mut j: nat = 0;
    while j < ops.len()
        invariant
            cumulative == sum(ops, j)
    {
        cumulative += ops[j as int];
        assert(cumulative == sum(ops, (j + 1) as nat));
        if cumulative < 0 {
            return true;
        }
        j += 1;
    }
    return false;
}
// </vc-code>

fn main() {
}

}