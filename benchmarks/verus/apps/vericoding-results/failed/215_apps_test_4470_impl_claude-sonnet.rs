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
/* helper modified by LLM (iteration 5): added explicit proof blocks with assertion details */
proof fn lemma_reduce_divides(n: nat, d: nat)
    requires
        n > 0,
        d > 1,
        n % d == 0,
        (d == 2 || d == 3 || d == 5),
    ensures
        reduce_by_factors_235(n) == reduce_by_factors_235(n / d),
    decreases n
{
    proof {
        if d == 2 {
            assert(n % 2 == 0);
            assert(reduce_by_factors_235(n) == reduce_by_factors_235(n / 2)) by {
                reveal(reduce_by_factors_235);
            };
        } else if d == 3 {
            assert(n % 3 == 0);
            assert(reduce_by_factors_235(n) == reduce_by_factors_235(n / 3)) by {
                reveal(reduce_by_factors_235);
            };
        } else if d == 5 {
            assert(n % 5 == 0);
            assert(reduce_by_factors_235(n) == reduce_by_factors_235(n / 5)) by {
                reveal(reduce_by_factors_235);
            };
        }
    }
}

proof fn lemma_min_moves_divides(n: nat, d: nat, cost: nat)
    requires
        n > 0,
        d > 1,
        n % d == 0,
        can_reach_one(n),
        cost > 0,
        (d == 2 || d == 3 || d == 5),
        (d == 2 ==> cost == 1),
        (d == 3 ==> cost == 2),
        (d == 5 ==> cost == 3),
    ensures
        can_reach_one(n / d),
        min_moves_to_one(n) == cost + min_moves_to_one(n / d),
    decreases n
{
    proof {
        lemma_reduce_divides(n, d);
        assert(reduce_by_factors_235(n) == reduce_by_factors_235(n / d));
        assert(reduce_by_factors_235(n) == 1);
        assert(reduce_by_factors_235(n / d) == 1);
        assert(can_reach_one(n / d));
        
        if d == 2 {
            assert(n % 2 == 0);
            assert(min_moves_to_one(n) == 1 + min_moves_to_one(n / 2)) by {
                reveal(min_moves_to_one);
            };
        } else if d == 3 {
            assert(n % 3 == 0);
            assert(min_moves_to_one(n) == 2 + min_moves_to_one(n / 3)) by {
                reveal(min_moves_to_one);
            };
        } else if d == 5 {
            assert(n % 5 == 0);
            assert(min_moves_to_one(n) == 3 + min_moves_to_one(n / 5)) by {
                reveal(min_moves_to_one);
            };
        }
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
    /* code modified by LLM (iteration 5): fixed overflow issues with proper bounds checking */
    let mut current = n;
    let mut moves: u8 = 0;
    
    while current != 1
        invariant
            current > 0,
            moves <= 100,
            n > 0,
            can_reach_one(n as nat) ==> can_reach_one(current as nat),
            can_reach_one(n as nat) ==> moves as nat + min_moves_to_one(current as nat) == min_moves_to_one(n as nat),
            !can_reach_one(n as nat) ==> reduce_by_factors_235(current as nat) != 1,
        decreases current
    {
        if current % 2 == 0 {
            proof {
                if can_reach_one(n as nat) {
                    lemma_min_moves_divides(current as nat, 2, 1);
                }
            }
            current = current / 2;
            if moves <= 99 {
                moves = moves + 1;
            } else {
                return -1;
            }
        } else if current % 3 == 0 {
            proof {
                if can_reach_one(n as nat) {
                    lemma_min_moves_divides(current as nat, 3, 2);
                }
            }
            current = current / 3;
            if moves <= 98 {
                moves = moves + 2;
            } else {
                return -1;
            }
        } else if current % 5 == 0 {
            proof {
                if can_reach_one(n as nat) {
                    lemma_min_moves_divides(current as nat, 5, 3);
                }
            }
            current = current / 5;
            if moves <= 97 {
                moves = moves + 3;
            } else {
                return -1;
            }
        } else {
            return -1;
        }
    }
    
    moves as i8
}
// </vc-code>


}

fn main() {}