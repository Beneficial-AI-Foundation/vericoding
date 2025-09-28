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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures result@ == correct_pronunciation(n as int)
// </vc-spec>
// <vc-code>
{
    let ones_digit = n % 10;
    let mut result = Vec::new();
    
    if ones_digit == 2 || ones_digit == 4 || ones_digit == 5 || ones_digit == 7 || ones_digit == 9 {
        result.push('h');
        result.push('o');
        result.push('n');
        result.push('\n');
    } else if ones_digit == 0 || ones_digit == 1 || ones_digit == 6 || ones_digit == 8 {
        result.push('p');
        result.push('o');
        result.push('n');
        result.push('\n');
    } else {
        result.push('b');
        result.push('o');
        result.push('n');
        result.push('\n');
    }
    
    assert(result.len() == 4);
    assert(result@.len() == 4);
    
    if ones_digit == 2 || ones_digit == 4 || ones_digit == 5 || ones_digit == 7 || ones_digit == 9 {
        assert(is_hon_digit(ones_digit as int));
        assert(result@ == seq!['h', 'o', 'n', '\n']);
    } else if ones_digit == 0 || ones_digit == 1 || ones_digit == 6 || ones_digit == 8 {
        assert(is_pon_digit(ones_digit as int));
        assert(result@ == seq!['p', 'o', 'n', '\n']);
    } else {
        assert(ones_digit == 3);
        assert(is_bon_digit(ones_digit as int));
        assert(result@ == seq!['b', 'o', 'n', '\n']);
    }
    
    result
}
// </vc-code>


}

fn main() {}