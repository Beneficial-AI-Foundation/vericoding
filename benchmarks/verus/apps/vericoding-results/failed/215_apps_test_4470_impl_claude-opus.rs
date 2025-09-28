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
/* helper modified by LLM (iteration 5): Fixed lemma assertions to only check when divisible, added stronger bound proof */
proof fn lemma_reduce_maintains_235(n: nat)
    requires
        n > 0,
        only_factors_235(n),
    ensures
        n == 1 || (n % 2 == 0 && only_factors_235(n / 2)) || (n % 3 == 0 && only_factors_235(n / 3)) || (n % 5 == 0 && only_factors_235(n / 5)),
    decreases n
{
    assert(reduce_by_factors_235(n) == 1);
    if n != 1 {
        if n % 2 == 0 {
            assert(reduce_by_factors_235(n / 2) == 1);
        } else if n % 3 == 0 {
            assert(reduce_by_factors_235(n / 3) == 1);
        } else if n % 5 == 0 {
            assert(reduce_by_factors_235(n / 5) == 1);
        } else {
            assert(reduce_by_factors_235(n) == n);
            assert(false);
        }
    }
}

fn check_only_235(n: u8) -> (result: bool)
    requires
        n > 0,
    ensures
        result == only_factors_235(n as nat),
    decreases n
{
    let mut current = n;
    while current > 1
        invariant
            current > 0,
            only_factors_235(n as nat) == only_factors_235(current as nat),
        decreases current
    {
        if current % 2 == 0 {
            current = current / 2;
        } else if current % 3 == 0 {
            current = current / 3;
        } else if current % 5 == 0 {
            current = current / 5;
        } else {
            assert(reduce_by_factors_235(current as nat) == current as nat);
            return false;
        }
    }
    assert(current == 1);
    assert(reduce_by_factors_235(current as nat) == 1);
    true
}

/* helper modified by LLM (iteration 5): Fixed conditional assertions in lemma */
proof fn lemma_min_moves_step(n: nat)
    requires
        n > 1,
        only_factors_235(n),
    ensures
        n % 2 == 0 ==> only_factors_235(n / 2) && min_moves_to_one(n) == 1 + min_moves_to_one(n / 2),
        n % 3 == 0 ==> only_factors_235(n / 3) && min_moves_to_one(n) == 2 + min_moves_to_one(n / 3),
        n % 5 == 0 ==> only_factors_235(n / 5) && min_moves_to_one(n) == 3 + min_moves_to_one(n / 5),
{
    lemma_reduce_maintains_235(n);
    if n % 2 == 0 {
        assert(only_factors_235(n / 2));
        assert(min_moves_to_one(n) == 1 + min_moves_to_one(n / 2));
    } else if n % 3 == 0 {
        assert(only_factors_235(n / 3));
        assert(min_moves_to_one(n) == 2 + min_moves_to_one(n / 3));
    } else if n % 5 == 0 {
        assert(only_factors_235(n / 5));
        assert(min_moves_to_one(n) == 3 + min_moves_to_one(n / 5));
    }
}

/* helper modified by LLM (iteration 5): Strengthened bound proof with explicit upper bound */
proof fn lemma_moves_bound(n: nat)
    requires
        n > 0,
        n <= 255,
        only_factors_235(n),
    ensures
        min_moves_to_one(n) <= 40,
    decreases n
{
    if n > 1 {
        lemma_reduce_maintains_235(n);
        lemma_min_moves_step(n);
        if n % 2 == 0 {
            assert(n / 2 <= 127);
            lemma_moves_bound(n / 2);
            assert(min_moves_to_one(n) == 1 + min_moves_to_one(n / 2));
            assert(min_moves_to_one(n / 2) <= 40);
            assert(min_moves_to_one(n) <= 41);
        } else if n % 3 == 0 {
            assert(n / 3 <= 85);
            lemma_moves_bound(n / 3);
            assert(min_moves_to_one(n) == 2 + min_moves_to_one(n / 3));
            assert(min_moves_to_one(n / 3) <= 40);
            assert(min_moves_to_one(n) <= 42);
        } else if n % 5 == 0 {
            assert(n / 5 <= 51);
            lemma_moves_bound(n / 5);
            assert(min_moves_to_one(n) == 3 + min_moves_to_one(n / 5));
            assert(min_moves_to_one(n / 5) <= 40);
            assert(min_moves_to_one(n) <= 43);
        }
    } else {
        assert(n == 1);
        assert(min_moves_to_one(1) == 0);
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
    /* code modified by LLM (iteration 5): Updated invariants for tighter bound */
    if !check_only_235(n) {
        return -1;
    }
    
    let mut current = n;
    let mut moves: u8 = 0;
    
    proof {
        lemma_moves_bound(n as nat);
    }
    
    while current > 1
        invariant
            current > 0,
            only_factors_235(current as nat),
            moves as nat + min_moves_to_one(current as nat) == min_moves_to_one(n as nat),
            min_moves_to_one(n as nat) <= 40,
            moves <= 40,
        decreases current
    {
        proof {
            lemma_reduce_maintains_235(current as nat);
            lemma_min_moves_step(current as nat);
        }
        
        if current % 2 == 0 {
            current = current / 2;
            moves = moves + 1;
        } else if current % 3 == 0 {
            current = current / 3;
            moves = moves + 2;
        } else if current % 5 == 0 {
            current = current / 5;
            moves = moves + 3;
        } else {
            assert(false);
        }
    }
    
    assert(current == 1);
    assert(min_moves_to_one(1) == 0);
    moves as i8
}
// </vc-code>


}

fn main() {}