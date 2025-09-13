// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn digit_sum(n: int) -> int;
spec fn int_to_string(n: int) -> Seq<char>;

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0 &&
    exists|k: int| k >= 1 && k <= 10000 && stdin_input == int_to_string(k).add(seq!['\n'])
}

spec fn kth_perfect_number(k: int) -> int
    recommends k >= 1 && k <= 10000
{
    if k == 1 { 19 }
    else if k == 2 { 28 }
    else if k == 3 { 37 }
    else if k == 4 { 46 }
    else if k == 5 { 55 }
    else if k == 6 { 64 }
    else if k == 7 { 73 }
    else if k == 8 { 82 }
    else if k == 9 { 91 }
    else if k == 10 { 109 }
    else { 10 * (k - 9) + 99 }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(stdin_input)
    ensures exists|k: int| k >= 1 && k <= 10000 && 
        stdin_input == int_to_string(k).add(seq!['\n']) &&
        result == int_to_string(kth_perfect_number(k)).add(seq!['\n'])
    ensures result.len() > 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    arbitrary()
}
// </vc-code>


}

fn main() {}