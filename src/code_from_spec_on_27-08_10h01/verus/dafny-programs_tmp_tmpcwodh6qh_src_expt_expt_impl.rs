use vstd::prelude::*;

verus! {

spec fn expt(b: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { b * expt(b, (n - 1) as nat) }
}

// <vc-helpers>
proof fn lemma_expt_preserves_invariant(b: int, i: nat)
    ensures expt(b, (i + 1) as nat) == expt(b, i as nat) * b
    decreases i
{
    if i == 0 {
        assert(expt(b, 1) == b * expt(b, 0));
        assert(expt(b, 0) == 1);
        assert(expt(b, 1) == b * 1);
        assert(expt(b, 1) == b);
        assert(expt(b, 0) * b == 1 * b);
        assert(expt(b, 0) * b == b);
    } else {
        assert(expt(b, (i + 1) as nat) == b * expt(b, i as nat));
    }
}

spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn expt_method(b: i32, n: u32) -> (res: i32)
    ensures res == expt(b as int, n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result = 1i32;
    let mut i = 0u32;
    while i < n
        invariant
            0 <= i <= n,
            result == expt(b as int, i as nat),
            abs_int(result as int) <= i32::MAX,
            (result as int) * (b as int) <= i32::MAX,
            (result as int) * (b as int) >= i32::MIN,
        decreases n - i
    {
        proof {
            lemma_expt_preserves_invariant(b as int, i as nat);
        }
        result = result * b;
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}