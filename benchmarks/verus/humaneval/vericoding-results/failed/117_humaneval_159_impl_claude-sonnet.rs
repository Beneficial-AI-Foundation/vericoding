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
/* helper modified by LLM (iteration 5): added overflow prevention helper with stronger bounds */
fn safe_add_i8(a: i8, b: i8) -> (result: i8)
    requires
        a as int + b as int <= i8::MAX as int,
        a >= 0,
        b >= 0,
    ensures result as int == a as int + b as int
{
    a + b
}

/* helper modified by LLM (iteration 5): added safe subtraction helper */
fn safe_sub_i8(a: i8, b: i8) -> (result: i8)
    requires
        a >= b,
        a >= 0,
        b >= 0,
    ensures result as int == a as int - b as int
{
    a - b
}
// </vc-helpers>

// <vc-spec>
fn eat(number: i8, need: i8, remaining: i8) -> (result: Vec<i8>)
    requires valid_input(number as int, need as int, remaining as int)
    ensures valid_result(result@.map(|i, x| x as int), number as int, need as int, remaining as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed ghost context for int casts */
    let eaten_by_rabbit = if need <= remaining { need } else { remaining };
    
    proof {
        assert(eaten_by_rabbit <= remaining);
        assert(eaten_by_rabbit <= need);
        assert(eaten_by_rabbit >= 0);
        assert(eaten_by_rabbit == can_eat(need as int, remaining as int));
        assert(number as int <= 1000);
        assert(eaten_by_rabbit as int <= remaining as int);
        assert(remaining as int <= 1000);
        assert(eaten_by_rabbit as int <= 1000);
        assert(number as int + eaten_by_rabbit as int <= 2000);
        assert(i8::MAX as int == 127);
    }
    
    // Check if the sum would overflow i8
    proof {
        if number as int + eaten_by_rabbit as int <= i8::MAX as int {
            assert(number as int + eaten_by_rabbit as int <= 127);
        }
    }
    
    let total_eaten_count = safe_add_i8(number, eaten_by_rabbit);
    let carrots_remaining = safe_sub_i8(remaining, eaten_by_rabbit);
    
    let mut result = Vec::new();
    result.push(total_eaten_count);
    result.push(carrots_remaining);
    
    proof {
        assert(result@.len() == 2);
        assert(result@[0] == total_eaten_count);
        assert(result@[1] == carrots_remaining);
        assert(total_eaten_count as int == total_eaten(number as int, need as int, remaining as int));
        assert(carrots_remaining as int == carrots_left(need as int, remaining as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}