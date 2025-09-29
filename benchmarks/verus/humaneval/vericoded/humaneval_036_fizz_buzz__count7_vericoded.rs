// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count7_r(x: nat) -> nat 
    decreases x
{
    let lst = if x % 10 == 7 { 1 as nat } else { 0 as nat };
    if x < 10 { lst } else { lst + count7_r(x / 10) }
}

spec fn sum(s: Seq<int>) -> int 
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): lemma decomposing count7_r into last digit and rest */
proof fn count7_r_decompose(x: nat)
    ensures count7_r(x) == (if x % 10 == 7 { 1 as nat } else { 0 as nat }) + count7_r(x / 10),
    decreases x
{
    if x < 10 {
        if x % 10 == 7 {
            assert(count7_r(x) == 1);
            assert(count7_r(x / 10) == 0);
            assert(count7_r(x) == 1 + 0);
        } else {
            assert(count7_r(x) == 0);
            assert(count7_r(x / 10) == 0);
            assert(count7_r(x) == 0 + 0);
        }
    } else {
        assert(count7_r(x) == (if x % 10 == 7 { 1 as nat } else { 0 as nat }) + count7_r(x / 10));
    }
}

/* helper modified by LLM (iteration 4): lemma bounding count7_r for u8 range */
proof fn count7_r_le_3(x: nat)
    requires x <= 255,
    ensures count7_r(x) <= 3,
    decreases x
{
    if x < 10 {
        assert(count7_r(x) <= 1);
    } else if x < 100 {
        let y = x / 10;
        count7_r_le_3(y);
        count7_r_decompose(x);
        assert(count7_r(x) <= 2);
    } else {
        let y = x / 10; // y < 26 for x <= 255
        if y < 10 {
            count7_r_le_3(y);
            count7_r_decompose(x);
            assert(count7_r(x) <= 2);
        } else {
            let z = y / 10;
            count7_r_le_3(z);
            count7_r_decompose(y);
            assert(count7_r(y) <= 2);
            count7_r_decompose(x);
            assert(count7_r(x) <= 3);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn count7(x: u8) -> (count: u8)
    ensures count as nat == count7_r(x as nat)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): maintain invariant using decomposition lemma and bounding lemma */
{
    let mut n: u8 = x;
    let mut c: u8 = 0;
    proof {
        count7_r_le_3(x as nat);
        assert((c as nat) + count7_r(n as nat) == count7_r(x as nat));
        assert((c as nat) <= 3);
    }
    while n > 0
        invariant
            (c as nat) + count7_r(n as nat) == count7_r(x as nat),
            (c as nat) <= 3,
        decreases n as nat
    {
        let old_n = n;
        let old_c = c;
        proof {
            count7_r_decompose(old_n as nat);
        }
        if old_n % 10u8 == 7u8 {
            c = old_c + 1;
        } else {
            c = old_c;
        }
        n = old_n / 10u8;
        proof {
            // preserve invariant using decomposition and previous invariant
            assert((old_c as nat) + count7_r(old_n as nat) == count7_r(x as nat));
            assert(count7_r(old_n as nat) == (if old_n % 10u8 == 7u8 { 1 as nat } else { 0 as nat }) + count7_r((old_n / 10u8) as nat));
            assert((c as nat) + count7_r(n as nat) == count7_r(x as nat));
            count7_r_le_3(x as nat);
            assert((c as nat) <= 3);
        }
    }
    c
}

// </vc-code>


}

fn main() {}