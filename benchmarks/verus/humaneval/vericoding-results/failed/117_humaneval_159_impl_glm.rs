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
fn eat(number: i8, need: i8, remaining: i8) -> (result: Vec<i8>)
    requires valid_input(number as int, need as int, remaining as int)
    ensures valid_result(result@.map(|i, x| x as int), number as int, need as int, remaining as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use i32 for intermediate computation and truncate to i8 */
    let eaten = if need <= remaining { need as i32 } else { remaining as i32 };
    let total = number as i32 + eaten;
    let left = remaining as i32 - eaten;
    let total_i8 = #[verifier::truncate] total as i8;
    let left_i8 = #[verifier::truncate] left as i8;
    vec![total_i8, left_i8]
}
// </vc-code>


}

fn main() {}