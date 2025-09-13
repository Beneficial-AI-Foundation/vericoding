// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn extract_numbers(input: &str, pos: int, acc: Seq<int>, current: &str) -> Seq<int>;

spec fn valid_input_format(input: &str) -> bool {
    input.len() > 0 &&
    {
        let nums = extract_numbers(input, 0, seq![], "");
        nums.len() >= 3 && 
        (forall|i: int| 0 <= i < 3 ==> 1 <= nums[i] <= 100)
    }
}

spec fn parse_three_ints_func(input: &str) -> (int, int, int) {
    let nums = extract_numbers(input, 0, seq![], "");
    (nums[0], nums[1], nums[2])
}

spec fn can_distribute_equally(a: int, b: int, c: int) -> bool {
    a + b == c || b + c == a || c + a == b
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires input.len() > 0
    requires valid_input_format(input)
    ensures result == "Yes\n" || result == "No\n"
    ensures ({
        let numbers = parse_three_ints_func(input);
        let a = numbers.0;
        let b = numbers.1; 
        let c = numbers.2;
        (result == "Yes\n") <==> can_distribute_equally(a, b, c)
    })
    ensures ({
        let numbers = parse_three_ints_func(input);
        numbers.0 >= 1 && numbers.1 >= 1 && numbers.2 >= 1 &&
        numbers.0 <= 100 && numbers.1 <= 100 && numbers.2 <= 100
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    "No\n".to_string()
}
// </vc-code>


}

fn main() {}