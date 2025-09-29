// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 999
}

spec fn is_hon_digit(digit: int) -> bool {
    digit == 2 || digit == 4 || digit == 5 || digit == 7 || digit == 9
}

spec fn is_pon_digit(digit: int) -> bool {
    digit == 0 || digit == 1 || digit == 6 || digit == 8
}

spec fn is_bon_digit(digit: int) -> bool {
    digit == 3
}

spec fn correct_pronunciation(n: int) -> Seq<char> {
    let ones_digit = n % 10;
    if is_hon_digit(ones_digit) {
        seq!['h', 'o', 'n', '\n']
    } else if is_pon_digit(ones_digit) {
        seq!['p', 'o', 'n', '\n']
    } else {
        seq!['b', 'o', 'n', '\n']
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): runtime pronunciation vector builder */
fn pronunciation_vec(n: i8) -> (v: Vec<char>)
    requires valid_input(n as int)
    ensures v@ == correct_pronunciation(n as int)
{
    let mut vec: Vec<char> = Vec::new();
    let ones: i8 = n % 10;
    if ones == 2 || ones == 4 || ones == 5 || ones == 7 || ones == 9 {
        vec.push('h');
        vec.push('o');
        vec.push('n');
        vec.push('\n');
    } else if ones == 0 || ones == 1 || ones == 6 || ones == 8 {
        vec.push('p');
        vec.push('o');
        vec.push('n');
        vec.push('\n');
    } else {
        vec.push('b');
        vec.push('o');
        vec.push('n');
        vec.push('\n');
    }
    vec
}

spec fn pronunciation_seq(n: int) -> Seq<char> {
    correct_pronunciation(n)
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures result@ == correct_pronunciation(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use runtime helper to build pronunciation Vec<char> */
    let result: Vec<char> = pronunciation_vec(n);
    result
}

// </vc-code>


}

fn main() {}