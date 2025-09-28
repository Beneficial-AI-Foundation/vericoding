// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(number: int, need: int, remaining: int) -> bool
{
    0 <= number <= 1000 && 0 <= need <= 1000 && 0 <= remaining <= 1000
}

spec fn can_eat(need: int, remaining: int) -> int
{
    if need <= remaining { need } else { remaining }
}

spec fn total_eaten(number: int, need: int, remaining: int) -> int
{
    number + can_eat(need, remaining)
}

spec fn carrots_left(need: int, remaining: int) -> int
{
    remaining - can_eat(need, remaining)
}

spec fn valid_result(result: Seq<int>, number: int, need: int, remaining: int) -> bool
{
    result.len() == 2 &&
    result[0] == total_eaten(number, need, remaining) &&
    result[1] == carrots_left(need, remaining) &&
    result[0] >= number &&
    result[1] >= 0 &&
    result[1] <= remaining
}
// </vc-preamble>

// <vc-helpers>
proof fn can_eat_proof(need: int, remaining: int) -> (amount: int)
    ensures
        amount == can_eat(need, remaining),
        amount >= 0,
        amount == if need <= remaining { need } else { remaining }
{
    if need <= remaining {
        need
    } else {
        remaining
    }
}

type Triple = (int, int, int);

proof fn total_eaten_proof(number: int, need: int, remaining: int) -> (result: Triple)
    ensures
        result.0 == number,
        result.1 == need,
        result.2 == remaining,
        total_eaten(number, need, remaining) == number + can_eat(need, remaining)
{
    (number, need, remaining)
}

proof fn carrots_left_proof(need: int, remaining: int) -> (result: int)
    ensures
        result == carrots_left(need, remaining),
        result == remaining - can_eat(need, remaining),
        result >= 0,
        result <= remaining
{
    let eaten = can_eat(need, remaining);
    proof {
        assert(eaten <= remaining);
    }
    remaining - eaten
}
// </vc-helpers>

// <vc-spec>
fn eat(number: i8, need: i8, remaining: i8) -> (result: Vec<i8>)
    requires valid_input(number as int, need as int, remaining as int)
    ensures valid_result(result@.map(|i, x| x as int), number as int, need as int, remaining as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by removing empty decreases clause and using ghost variable */
    let ghost_number: int = number as int;
    let ghost_need: int = need as int;
    let ghost_remaining: int = remaining as int;
    
    let amount = can_eat(ghost_need, ghost_remaining);
    let total = ghost_number + amount;
    let left = ghost_remaining - amount;
    
    let mut result = Vec::new();
    result.push(total as i8);
    result.push(left as i8);
    
    result
}
// </vc-code>


}

fn main() {}