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
/* helper modified by LLM (iteration 4): prove can_eat nonnegativity */
proof fn can_eat_nonneg(need: i8, remaining: i8)
    requires
        0 <= need as int,
        0 <= remaining as int,
    ensures
        can_eat(need as int, remaining as int) >= 0,
{
    if need as int <= remaining as int {
        assert(can_eat(need as int, remaining as int) == need as int);
        assert(can_eat(need as int, remaining as int) >= 0);
    } else {
        assert(can_eat(need as int, remaining as int) == remaining as int);
        assert(can_eat(need as int, remaining as int) >= 0);
    }
}

// </vc-helpers>

// <vc-spec>
fn eat(number: i8, need: i8, remaining: i8) -> (result: Vec<i8>)
    requires valid_input(number as int, need as int, remaining as int)
    ensures valid_result(result@.map(|i, x| x as int), number as int, need as int, remaining as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute eaten, total, left and prove spec in proof block */
    let eaten_i8: i8 = if need <= remaining { need } else { remaining };
    let total_i8: i8 = number + eaten_i8;
    let left_i8: i8 = remaining - eaten_i8;
    let mut v: Vec<i8> = Vec::new();
    v.push(total_i8);
    v.push(left_i8);
    proof {
        let total = total_i8 as int;
        let left = left_i8 as int;
        let num = number as int;
        let nd = need as int;
        let rem = remaining as int;
        assert(v@.len() == 2);
        assert(v@[0] as int == total);
        assert(v@[1] as int == left);
        if nd <= rem {
            assert(can_eat(nd, rem) == nd);
        } else {
            assert(can_eat(nd, rem) == rem);
        }
        assert(total == num + can_eat(nd, rem));
        assert(left == rem - can_eat(nd, rem));
        assert(total >= num);
        assert(left >= 0);
        assert(left <= rem);
    }
    v
}

// </vc-code>


}

fn main() {}