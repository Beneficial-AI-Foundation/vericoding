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
// </vc-helpers>

// <vc-spec>
fn eat(number: int, need: int, remaining: int) -> (result: Vec<int>)
    requires valid_input(number, need, remaining)
    ensures valid_result(result@, number, need, remaining)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}