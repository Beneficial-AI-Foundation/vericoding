// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: nat) -> bool {
    n > 0
}

spec fn can_reach_one(n: nat) -> bool
    recommends n > 0
{
    only_factors_235(n)
}

spec fn only_factors_235(n: nat) -> bool
    recommends n > 0
{
    reduce_by_factors_235(n) == 1
}

spec fn reduce_by_factors_235(n: nat) -> nat
    recommends n > 0
    decreases n
    when n > 0
{
    if n == 1 {
        1
    } else if n % 2 == 0 {
        reduce_by_factors_235(n / 2)
    } else if n % 3 == 0 {
        reduce_by_factors_235(n / 3)
    } else if n % 5 == 0 {
        reduce_by_factors_235(n / 5)
    } else {
        n
    }
}

spec fn min_moves_to_one(n: nat) -> nat
    recommends n > 0 && can_reach_one(n)
    decreases n
    when n > 0
{
    if n == 1 {
        0
    } else if n % 2 == 0 {
        1 + min_moves_to_one(n / 2)
    } else if n % 3 == 0 {
        2 + min_moves_to_one(n / 3)
    } else if n % 5 == 0 {
        3 + min_moves_to_one(n / 5)
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): div2 can_reach */
proof fn lemma_div2_can_reach(n: nat)
    requires
        n > 0,
        n % 2 == 0,
    ensures
        can_reach_one(n) <==> can_reach_one(n / 2),
    decreases n
{
    assert(reduce_by_factors_235(n) == reduce_by_factors_235(n / 2));
    assert(can_reach_one(n) <==> can_reach_one(n / 2));
}

/* helper modified by LLM (iteration 3): div3 can_reach (requires not divisible by 2) */
proof fn lemma_div3_can_reach(n: nat)
    requires
        n > 0,
        n % 3 == 0,
        n % 2 != 0,
    ensures
        can_reach_one(n) <==> can_reach_one(n / 3),
    decreases n
{
    assert(reduce_by_factors_235(n) == reduce_by_factors_235(n / 3));
    assert(can_reach_one(n) <==> can_reach_one(n / 3));
}

/* helper modified by LLM (iteration 3): div5 can_reach (requires not divisible by 2 or 3) */
proof fn lemma_div5_can_reach(n: nat)
    requires
        n > 0,
        n % 5 == 0,
        n % 2 != 0,
        n % 3 != 0,
    ensures
        can_reach_one(n) <==> can_reach_one(n / 5),
    decreases n
{
    assert(reduce_by_factors_235(n) == reduce_by_factors_235(n / 5));
    assert(can_reach_one(n) <==> can_reach_one(n / 5));
}

/* helper modified by LLM (iteration 3): min_moves div2 */
proof fn lemma_min_moves_div2(n: nat)
    requires
        n > 0,
        n % 2 == 0,
        can_reach_one(n),
    ensures
        min_moves_to_one(n) == 1 + min_moves_to_one(n / 2),
    decreases n
{
    assert(min_moves_to_one(n) == 1 + min_moves_to_one(n / 2));
}

/* helper modified by LLM (iteration 3): min_moves div3 (requires not divisible by 2) */
proof fn lemma_min_moves_div3(n: nat)
    requires
        n > 0,
        n % 3 == 0,
        n % 2 != 0,
        can_reach_one(n),
    ensures
        min_moves_to_one(n) == 2 + min_moves_to_one(n / 3),
    decreases n
{
    assert(min_moves_to_one(n) == 2 + min_moves_to_one(n / 3));
}

/* helper modified by LLM (iteration 3): min_moves div5 (requires not divisible by 2 or 3) */
proof fn lemma_min_moves_div5(n: nat)
    requires
        n > 0,
        n % 5 == 0,
        n % 2 != 0,
        n % 3 != 0,
        can_reach_one(n),
    ensures
        min_moves_to_one(n) == 3 + min_moves_to_one(n / 5),
    decreases n
{
    assert(min_moves_to_one(n) == 3 + min_moves_to_one(n / 5));
}

/* helper modified by LLM (iteration 3): not divisible implies cannot reach */
proof fn lemma_not_divisible(n: nat)
    requires
        n > 1,
        n % 2 != 0,
        n % 3 != 0,
        n % 5 != 0,
    ensures
        !can_reach_one(n),
    decreases n
{
    assert(reduce_by_factors_235(n) == n);
    assert(reduce_by_factors_235(n) != 1);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: u8) -> (result: i8)
    requires
        valid_input(n as nat),
    ensures
        result >= -1,
        result == -1 <==> !can_reach_one(n as nat),
        result >= 0 ==> can_reach_one(n as nat) && result == min_moves_to_one(n as nat) as i8,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement solve loop with proofs and fix cast attribute placement */
    let mut cur: u8 = n;
    let mut acc: u8 = 0;
    while cur != 1 && (cur % 2 == 0 || cur % 3 == 0 || cur % 5 == 0)
        invariant
            cur as nat > 0,
            can_reach_one(n as nat) <==> can_reach_one(cur as nat),
            min_moves_to_one(n as nat) == (acc as nat) + min_moves_to_one(cur as nat),
        decreases cur as nat
    {
        if cur % 2 == 0 {
            let old = cur;
            cur = cur / 2;
            acc = acc + 1;
            proof {
                lemma_div2_can_reach(old as nat);
                if can_reach_one(old as nat) {
                    lemma_min_moves_div2(old as nat);
                }
            }
        } else if cur % 3 == 0 {
            let old = cur;
            cur = cur / 3;
            acc = acc + 2;
            proof {
                lemma_div3_can_reach(old as nat);
                if can_reach_one(old as nat) {
                    lemma_min_moves_div3(old as nat);
                }
            }
        } else {
            let old = cur;
            cur = cur / 5;
            acc = acc + 3;
            proof {
                lemma_div5_can_reach(old as nat);
                if can_reach_one(old as nat) {
                    lemma_min_moves_div5(old as nat);
                }
            }
        }
    }
    if cur == 1 {
        proof {
            assert(can_reach_one(1 as nat));
            assert(can_reach_one(n as nat));
            assert(min_moves_to_one(1 as nat) == 0);
            assert(min_moves_to_one(n as nat) == (acc as nat) + 0);
        }
        return (acc as i8)#[verifier::truncate];
    } else {
        proof {
            lemma_not_divisible(cur as nat);
            assert(!can_reach_one(n as nat));
        }
        return -1;
    }
}
// </vc-code>


}

fn main() {}