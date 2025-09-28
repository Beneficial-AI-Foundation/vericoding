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


proof fn lemma_min_moves_to_one_decreases(n: nat)
    requires
        n > 0,
        can_reach_one(n),
    ensures
        min_moves_to_one(n) >= 0,
        n % 2 == 0 ==> min_moves_to_one(n) > min_moves_to_one(n / 2),
        n % 3 == 0 ==> min_moves_to_one(n) > min_moves_to_one(n / 3),
        n % 5 == 0 ==> min_moves_to_one(n) > min_moves_to_one(n / 5),
    decreases n
{
    if n > 1 {
        if n % 2 == 0 {
            lemma_min_moves_to_one_decreases(n / 2);
        } else if n % 3 == 0 {
            lemma_min_moves_to_one_decreases(n / 3);
        } else if n % 5 == 0 {
            lemma_min_moves_to_one_decreases(n / 5);
        }
    }
}

proof fn lemma_only_factors_235_implies_divisible(n: nat)
    requires
        n > 1,
        only_factors_235(n),
    ensures
        n % 2 == 0 || n % 3 == 0 || n % 5 == 0,
    decreases n
{
    if n > 1 {
        if n % 2 != 0 && n % 3 != 0 && n % 5 != 0 {
            assert(reduce_by_factors_235(n) == n);
            assert(reduce_by_factors_235(n) != 1);
        }
    }
}

/* helper modified by LLM (iteration 5): fix return type for proof function */
proof fn check_can_reach_one(n: u8) -> (result: bool)
    requires 1 <= n
    ensures result == can_reach_one(n as nat)
{
    can_reach_one(n as nat)
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
    /* code modified by LLM (iteration 5): fix type mismatch error with explicit casting */
    if !check_can_reach_one(n) {
        return -1i8;
    } else {
        let mut current = n as u64;
        let mut moves: i8 = 0;
        
        while current > 1
            invariant
                current > 0,
                can_reach_one(current as nat),
                moves >= 0,
                moves == min_moves_to_one(current as nat) as i8,
            decreases current
        {
            proof {
                lemma_only_factors_235_implies_divisible(current as nat);
                lemma_min_moves_to_one_decreases(current as nat);
            }
            
            if current % 2 == 0 {
                current = current / 2;
                moves += 1;
            } else if current % 3 == 0 {
                current = current / 3;
                moves += 2;
            } else if current % 5 == 0 {
                current = current / 5;
                moves += 3;
            } else {
                proof { assert(false); }
                unreached();
            }
        }
        
        moves
    }
}
// </vc-code>


}

fn main() {}