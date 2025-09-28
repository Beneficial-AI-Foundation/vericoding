// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * power(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide lemma to unfold power at successor exponent */
proof fn power_succ(base: int, e: nat)
    ensures
        power(base, e + 1) == base * power(base, e),
{
    reveal(power);
}

// </vc-helpers>

// <vc-spec>
fn modp(n: i8, p: i8) -> (result: i8)
    requires 
        n >= 0 && p > 0,
    ensures 
        result >= 0 && result < p,
        result as int == power(2, n as nat) % (p as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): initialize ghost q and invoke helper lemma to justify power step */
    let p32: i32 = p as i32;
    let mut acc: i32 = 1;
    if acc >= p32 {
        acc = acc - p32;
    }
    let mut i: i8 = 0;
    let mut ghost q: int = 0;
    proof {
        assert(0 < p@);
        if 1 >= p@ {
            q = 1;
            assert(acc@ == 1 - p@);
            assert(power(2, 0 as nat) == 1);
            assert(q * p@ + acc@ == 1);
            assert(0 <= acc@);
            assert(acc@ < p@);
        } else {
            q = 0;
            assert(acc@ == 1);
            assert(power(2, 0 as nat) == 1);
            assert(q * p@ + acc@ == 1);
            assert(0 <= acc@);
            assert(acc@ < p@);
        }
    }
    while i < n
        invariant
            0 <= i@,
            i@ <= n@,
            0 < p@,
            0 <= acc@,
            acc@ < p@,
            power(2, i@ as nat) == q * p@ + acc@,
        decreases (n@ - i@)
    {
        let old_acc: i32 = acc;
        let two_acc: i32 = old_acc + old_acc;
        if two_acc >= p32 {
            acc = two_acc - p32;
            proof {
                power_succ(2, i@ as nat);
                assert(power(2, (i@ + 1) as nat) == 2 * power(2, i@ as nat));
                assert(power(2, i@ as nat) == q * p@ + old_acc@);
                assert(two_acc@ == old_acc@ + old_acc@);
                assert(0 <= old_acc@);
                assert(old_acc@ < p@);
                assert(two_acc@ < 2 * p@);
                assert(acc@ == two_acc@ - p@);
                assert(2 * old_acc@ == p@ + acc@);
                assert(2 * (q * p@ + old_acc@) == (2 * q) * p@ + 2 * old_acc@);
                assert((2 * q) * p@ + 2 * old_acc@ == (2 * q + 1) * p@ + acc@);
                q = 2 * q + 1;
                assert(0 <= acc@);
                assert(acc@ < p@);
            }
        } else {
            acc = two_acc;
            proof {
                power_succ(2, i@ as nat);
                assert(power(2, (i@ + 1) as nat) == 2 * power(2, i@ as nat));
                assert(power(2, i@ as nat) == q * p@ + old_acc@);
                assert(two_acc@ == old_acc@ + old_acc@);
                assert(2 * old_acc@ == acc@);
                assert(2 * (q * p@ + old_acc@) == (2 * q) * p@ + 2 * old_acc@);
                assert((2 * q) * p@ + 2 * old_acc@ == (2 * q) * p@ + acc@);
                q = 2 * q;
                assert(0 <= acc@);
                assert(acc@ < p@);
            }
        }
        // Safe increment (no overflow since i < n and n <= i8::MAX)
        i = i + 1;
    }
    let result: i8 = acc as i8;
    proof {
        assert(0 <= acc@);
        assert(acc@ < p@);
        assert(result@ == acc@);
    }
    result
}

// </vc-code>


}

fn main() {}