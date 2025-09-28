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
/* helper modified by LLM (iteration 5): removed `proof` keyword, functions that return `()` are not distinguished by `proof` keyword in Verus, and replaced with `fn` keyword */
fn mul_is_distrib_over_add(a: int, b: int, c: int)
    ensures a * (b + c) == a * b + a * c
{
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
/* code modified by LLM (iteration 5): simplify implementation to directly return the result of min_moves_to_one or -1 and remove unnecessary recursion and variable. */
{
    let n_nat = n as nat;

    if can_reach_one(n_nat) {
        min_moves_to_one(n_nat) as i8
    } else {
        -1
    }
}
// </vc-code>


}

fn main() {}