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
/* helper modified by LLM (iteration 3): [no logic changes from previous attempt] */
proof fn stuck_is_unreachable(n: nat)
    requires
        n > 1,
        n % 2 != 0,
        n % 3 != 0,
        n % 5 != 0,
    ensures !can_reach_one(n),
{
    assert(reduce_by_factors_235(n) == n);
    assert(can_reach_one(n) <==> (reduce_by_factors_235(n) == 1));
    if can_reach_one(n) {
        assert(reduce_by_factors_235(n) == 1);
        assert(n == 1);
        assert(false);
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
/* code modified by LLM (iteration 3): [fixed compilation error by moving ghost code into a proof block] */
{
    let mut current_n = n;
    let mut moves: i8 = 0;

    while current_n > 1
        invariant
            n > 0,
            current_n > 0,
            can_reach_one(n as nat) <==> can_reach_one(current_n as nat),
            can_reach_one(n as nat) ==> min_moves_to_one(n as nat) == moves as nat + min_moves_to_one(current_n as nat),
            moves >= 0,
        decreases current_n
    {
        if current_n % 2 == 0 {
            proof {
                assert(can_reach_one(current_n as nat) <==> can_reach_one(current_n as nat / 2));
                if can_reach_one(n as nat) {
                    assert(can_reach_one(current_n as nat));
                    assert(min_moves_to_one(current_n as nat) == 1 + min_moves_to_one(current_n as nat / 2));
                }
            }
            current_n = current_n / 2;
            moves = moves + 1;
        } else if current_n % 3 == 0 {
            proof {
                assert(can_reach_one(current_n as nat) <==> can_reach_one(current_n as nat / 3));
                if can_reach_one(n as nat) {
                    assert(can_reach_one(current_n as nat));
                    assert(min_moves_to_one(current_n as nat) == 2 + min_moves_to_one(current_n as nat / 3));
                }
            }
            current_n = current_n / 3;
            moves = moves + 2;
        } else if current_n % 5 == 0 {
            proof {
                assert(can_reach_one(current_n as nat) <==> can_reach_one(current_n as nat / 5));
                if can_reach_one(n as nat) {
                    assert(can_reach_one(current_n as nat));
                    assert(min_moves_to_one(current_n as nat) == 3 + min_moves_to_one(current_n as nat / 5));
                }
            }
            current_n = current_n / 5;
            moves = moves + 3;
        } else {
            proof {
                stuck_is_unreachable(current_n as nat);
                assert(!can_reach_one(current_n as nat));
            }
            return -1;
        }
    }

    proof {
        assert(current_n == 1);
        assert(can_reach_one(n as nat) <==> can_reach_one(1 as nat));
        assert(can_reach_one(1 as nat));
        assert(can_reach_one(n as nat));
        assert(min_moves_to_one(n as nat) == moves as nat + min_moves_to_one(1 as nat));
        assert(min_moves_to_one(1 as nat) == 0);
        assert(min_moves_to_one(n as nat) == moves as nat);
    }
    
    moves
}
// </vc-code>


}

fn main() {}