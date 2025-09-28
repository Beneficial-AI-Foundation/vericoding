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
/* helper modified by LLM (iteration 3): Changed types to i32 to fix compilation errors with ghost types */
fn can_eat_exe(need: i32, remaining: i32) -> i32
{
    if need <= remaining { need } else { remaining }
}

/* helper modified by LLM (iteration 3): Changed types to i32 to fix compilation errors with ghost types */
fn total_eaten_exe(number: i32, need: i32, remaining: i32) -> i32
{
    number + can_eat_exe(need, remaining)
}

/* helper modified by LLM (iteration 3): Changed types to i32 to fix compilation errors with ghost types */
fn carrots_left_exe(need: i32, remaining: i32) -> i32
{
    remaining - can_eat_exe(need, remaining)
}
// </vc-helpers>

// <vc-spec>
fn eat(number: i8, need: i8, remaining: i8) -> (result: Vec<i8>)
    requires valid_input(number as int, need as int, remaining as int)
    ensures valid_result(result@.map(|i, x| x as int), number as int, need as int, remaining as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed compilation by using i32 for computations */
    let need_i: i32 = need as i32;
    let remaining_i: i32 = remaining as i32;
    let eaten = can_eat_exe(need_i, remaining_i);
    let total_i = (number as i32) + eaten;
    let left_i = remaining_i - eaten;
    let mut result = Vec::new();
    result.push(total_i as i8);
    result.push(left_i as i8);
    result
}
// </vc-code>


}

fn main() {}