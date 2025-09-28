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
/* helper modified by LLM (iteration 5): [no changes, helper is correct] */
proof fn lemma_count7_r_unfold(n: nat)
    ensures count7_r(n) == (if n % 10 == 7 { 1 as nat } else { 0 as nat }) + (if n < 10 { 0 as nat } else { count7_r(n / 10) })
{
    reveal(count7_r);
}

/* helper modified by LLM (iteration 5): [no changes, helper is correct] */
proof fn lemma_count7_r_bound(x: u8)
    ensures count7_r(x as nat) <= 2
{
    let n = x as nat;
    lemma_count7_r_unfold(n);
    if n >= 10 {
        let n1 = n / 10;
        lemma_count7_r_unfold(n1);
        if n1 >= 10 {
            let n2 = n1 / 10;
            lemma_count7_r_unfold(n2);
            assert(n2 < 3); // x <= 255 -> n <= 255 -> n1 <= 25 -> n2 <= 2
            assert(n2 != 7);
            assert(count7_r(n2) == 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn count7(x: u8) -> (count: u8)
    ensures count as nat == count7_r(x as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [added invariants and moved proof call to fix verification] */
    let mut n = x;
    let mut count: u8 = 0;

    proof {
        lemma_count7_r_bound(x);
    }

    while n > 0
        invariant
            count7_r(x as nat) == count as nat + count7_r(n as nat),
            count as nat <= count7_r(x as nat),
            count7_r(x as nat) <= 2,
        decreases n
    {
        proof {
            lemma_count7_r_unfold(n as nat);
        }

        if n % 10 == 7 {
            count = count + 1;
        }
        n = n / 10;
    }

    proof {
        reveal(count7_r);
    }
    
    count
}
// </vc-code>


}

fn main() {}