// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count7_r(x: nat) -> nat
    decreases x
{
    let lst = if x % 10 == 7 { 1 } else { 0 };
    if x < 10 { lst } else { lst + count7_r(x / 10) }
}

spec fn sum(s: Seq<nat>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [updated comments, no logic change] */
fn count7(x: u8) -> (result: u8)
    ensures result as nat == count7_r(x as nat),
{
    let mut current = x;
    let mut count: u8 = 0;
    while current > 0
        invariant
            count7_r(x as nat) == count7_r(current as nat) + count as nat,
        decreases current
    {
        if current % 10 == 7 {
            count = count + 1;
        }
        current = current / 10;
    }
    count
}

/* helper modified by LLM (iteration 4): [updated comments, no logic change] */
proof fn lemma_sum_push(s: Seq<nat>, e: nat)
    ensures sum(s.push(e)) == sum(s) + e,
    decreases s.len(),
{
    if s.len() > 0 {
        assert(s.push(e).subrange(1, (s.len() + 1) as int) =~= s.subrange(1, s.len() as int).push(e));
        lemma_sum_push(s.subrange(1, s.len() as int), e);
    }
}
// </vc-helpers>

// <vc-spec>
fn fizz_buzz(n: u8) -> (result: u8)
    ensures result as nat == sum(
        Seq::new(n as nat, |i: int| 
            if 0 <= i < n as nat && (i % 11 == 0 || i % 13 == 0) { count7_r(i as nat) } else { 0 }
        )
    )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [fixed type casts for Seq::take from nat to int] */
    let mut i: u8 = 0;
    let mut total: u8 = 0;
    let ghost spec_seq = Seq::new(n as nat, |k: int| 
        if 0 <= k < n as nat && (k % 11 == 0 || k % 13 == 0) { count7_r(k as nat) } else { 0 }
    );

    while i < n
        invariant
            0 <= i <= n,
            total as nat == sum(spec_seq.take(i as int)),
        decreases n - i
    {
        proof {
            if i < n {
                assert(spec_seq.take((i + 1) as int) =~= spec_seq.take(i as int).push(spec_seq[i as int]));
                lemma_sum_push(spec_seq.take(i as int), spec_seq[i as int]);
            }
        }

        if i % 11 == 0 || i % 13 == 0 {
            let c = count7(i);
            total = total + c;
        }
        i = i + 1;
    }
    
    proof {
      assert(spec_seq.take(n as int) =~= spec_seq);
    }

    total
}
// </vc-code>


}

fn main() {}