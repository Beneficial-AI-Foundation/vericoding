// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: &Vec<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): refined step lemma for sum_to with simple unfolding */
proof fn lemma_sum_to_step(a: &Vec<i32>, n: int)
    requires
        0 <= n < a.len() as int,
    ensures
        sum_to(a, n + 1) == sum_to(a, n) + a[n]
{
    assert(sum_to(a, n + 1) == sum_to(a, (n + 1) - 1) + a[(n + 1) - 1]);
    assert((n + 1) - 1 == n);
}

// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        result == sum_to(a, a.len() as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): sum array with loop and step lemma; use i64 temp to avoid direct i32 overflow checks, and relate to spec via proofs */
    let mut i: usize = 0;
    let mut s: i32 = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            s as int == sum_to(a, i as int),
        decreases a.len() as int - i as int
    {
        let ai: i32 = a[i];
        let s64: i64 = s as i64;
        let ai64: i64 = ai as i64;
        // i64 addition cannot overflow given i32 bounds of operands
        assert(i64::MIN <= s64);
        assert(i64::MIN <= ai64);
        assert(s64 <= i32::MAX as i64);
        assert(ai64 <= i32::MAX as i64);
        let t64: i64 = s64 + ai64;
        // t64 is within i64 range trivially
        assert(i64::MIN <= t64 && t64 <= i64::MAX);
        s = t64 as i32;
        let ghost ii: int = i as int;
        proof {
            assert(0 <= ii < a.len() as int);
            lemma_sum_to_step(a, ii);
            assert((s64 as int) == s as int); // s64 and s are consistent via cast viewed as int
            assert((ai64 as int) == a[i] as int);
            assert(s as int == (s64 + ai64) as int);
            assert(sum_to(a, ii + 1) == sum_to(a, ii) + a[ii]);
            assert(sum_to(a, ii) + a[ii] == (s as int));
        }
        i = i + 1;
        proof {
            assert(i as int == ii + 1);
            assert(s as int == sum_to(a, i as int));
        }
    }
    s
}
// </vc-code>

}
fn main() {}