// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn extract_numbers(input: Seq<char>, index: int, acc: Seq<int>, current: Seq<char>) -> Seq<int> {
    Seq::empty()
}

spec fn valid_input_format(input: Seq<char>) -> bool {
    input.len() > 0 &&
    {
        let nums = extract_numbers(input, 0, Seq::empty(), Seq::empty());
        nums.len() >= 3 && 
        (forall|i: int| 0 <= i < 3 ==> #[trigger] nums[i] >= 1 && #[trigger] nums[i] <= 100)
    }
}

spec fn parse_three_ints_func(input: Seq<char>) -> (int, int, int) {
    let nums = extract_numbers(input, 0, Seq::empty(), Seq::empty());
    (nums[0], nums[1], nums[2])
}

spec fn can_distribute_equally(a: int, b: int, c: int) -> bool {
    a + b == c || b + c == a || c + a == b
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires 
        input.len() > 0,
        valid_input_format(input),
    ensures 
        result == seq!['Y', 'e', 's', '\n'] || result == seq!['N', 'o', '\n'],
        ({
            let numbers = parse_three_ints_func(input);
            let a = numbers.0;
            let b = numbers.1; 
            let c = numbers.2;
            (result == seq!['Y', 'e', 's', '\n']) <==> can_distribute_equally(a, b, c)
        }),
        ({
            let numbers = parse_three_ints_func(input);
            numbers.0 >= 1 && numbers.1 >= 1 && numbers.2 >= 1 &&
            numbers.0 <= 100 && numbers.1 <= 100 && numbers.2 <= 100
        }),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}