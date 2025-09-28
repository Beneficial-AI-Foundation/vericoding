// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= b <= a <= 20 && 1 <= c <= 20
}

spec fn remaining_water(a: int, b: int, c: int) -> int
    recommends valid_input(a, b, c)
{
    let available_space = a - b;
    let remaining = c - available_space;
    if remaining >= 0 { remaining } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added input length check */
proof fn lemma_remaining_water_bounds(a: int, b: int, c: int)
    requires
        valid_input(a, b, c),
    ensures
        0 <= remaining_water(a, b, c) <= c,
{
    let available_space = a - b;
    let remaining = c - available_space;
    if remaining >= 0 {
        assert(remaining_water(a, b, c) == remaining);
        assert(remaining <= c);
    } else {
        assert(remaining_water(a, b, c) == 0);
    }
}

proof fn lemma_remaining_water_computation(a: int, b: int, c: int)
    requires
        valid_input(a, b, c),
    ensures
        remaining_water(a, b, c) == if c > a - b { c - (a - b) } else { 0 },
{
    let available_space = a - b;
    let remaining = c - available_space;
}

fn parse_input(input: Vec<i8>) -> (result: (i8, i8, i8))
    requires
        input.len() >= 3,
    ensures
        result.0 == input[0] && result.1 == input[1] && result.2 == input[2],
{
    (input[0], input[1], input[2])
}

fn format_output(remaining: i8) -> (result: Vec<i8>)
    ensures
        result.len() == 1,
        result[0] == remaining,
{
    vec![remaining]
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<i8>) -> (result: Vec<i8>)
    requires input.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added input length check before parsing */
    if input.len() < 3 {
        return vec![0];
    }
    
    let (a, b, c) = parse_input(input);
    
    if a < 1 || a > 20 || b < 1 || b > 20 || c < 1 || c > 20 || b > a {
        return vec![0];
    }
    
    proof {
        assert(valid_input(a as int, b as int, c as int));
        lemma_remaining_water_bounds(a as int, b as int, c as int);
        lemma_remaining_water_computation(a as int, b as int, c as int);
    }
    
    let available_space = a - b;
    let remaining = if c > available_space {
        c - available_space
    } else {
        0
    };
    
    format_output(remaining)
}
// </vc-code>


}

fn main() {}