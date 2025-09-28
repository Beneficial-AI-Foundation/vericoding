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
/* helper modified by LLM (iteration 5): added helper to check if number can reach 1 and compute moves */
proof fn can_reach_one_implies_min_moves_defined(n: nat)
    requires
        can_reach_one(n),
    ensures
        min_moves_to_one(n) >= 0,
    decreases n
{
    if n == 1 {
        assert(min_moves_to_one(n) == 0);
    } else if n % 2 == 0 {
        can_reach_one_implies_min_moves_defined(n / 2);
        assert(min_moves_to_one(n) == 1 + min_moves_to_one(n / 2));
    } else if n % 3 == 0 {
        can_reach_one_implies_min_moves_defined(n / 3);
        assert(min_moves_to_one(n) == 2 + min_moves_to_one(n / 3));
    } else if n % 5 == 0 {
        can_reach_one_implies_min_moves_defined(n / 5);
        assert(min_moves_to_one(n) == 3 + min_moves_to_one(n / 5));
    }
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
    /* code modified by LLM (iteration 5): removed non-ghost nat conversion and used ghost expressions in invariants */
    let mut current = n;
    let mut moves = 0 as i8;

    while current != 1
        invariant
            current > 0,
            moves >= 0,
            can_reach_one(n as nat) ==> can_reach_one(current as nat),
            can_reach_one(n as nat) ==> moves <= min_moves_to_one(n as nat) as i8,
        decreases current
    {
        if current % 2 == 0 {
            current = current / 2;
            assert(can_reach_one(n as nat) ==> moves + 1 <= min_moves_to_one(n as nat) as i8);
            moves += 1;
        } else if current % 3 == 0 {
            current = current / 3;
            assert(can_reach_one(n as nat) ==> moves + 2 <= min_moves_to_one(n as nat) as i8);
            moves += 2;
        } else if current % 5 == 0 {
            current = current / 5;
            assert(can_reach_one(n as nat) ==> moves + 3 <= min_moves_to_one(n as nat) as i8);
            moves += 3;
        } else {
            break;
        }
    }

    if current == 1 {
        proof {
            if can_reach_one(n as nat) {
                assert(moves == min_moves_to_one(n as nat) as i8);
            }
        }
        moves
    } else {
        -1
    }
}
// </vc-code>


}

fn main() {}