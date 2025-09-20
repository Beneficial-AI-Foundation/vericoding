// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, digits: Seq<char>) -> bool {
    n > 0 && digits.len() == n && forall|i: int| 0 <= i < digits.len() ==> #[trigger] digits[i] >= '0' && #[trigger] digits[i] <= '9'
}

spec fn modify_string(s: Seq<char>, index: int) -> Seq<char> {
    let key = if s[index] == '0' { 0 } else { 10 - (s[index] as int - '0' as int) };
    let transformed = transform_digits(s, key);
    rotate_string(transformed, index)
}

spec fn transform_digits(s: Seq<char>, key: int) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let digit = (s[0] as int - '0' as int + key) % 10;
        seq![('0' as int + digit) as char].add(transform_digits(s.skip(1), key))
    }
}

spec fn rotate_string(s: Seq<char>, index: int) -> Seq<char> {
    if s.len() == 0 {
        seq![]
    } else {
        s.skip(index).add(s.take(index))
    }
}

spec fn is_all_digits(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9'
}

spec fn parse_input(input: Seq<char>) -> Seq<Seq<char>>
    decreases input.len()
{
    parse_input_helper(input, 0, seq![], seq![])
}

spec fn parse_input_helper(input: Seq<char>, i: int, current_line: Seq<char>, lines: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases input.len() - i
{
    if i >= input.len() {
        if current_line.len() > 0 { lines.push(current_line) } else { lines }
    } else if input[i] == '\n' {
        parse_input_helper(input, i + 1, seq![], lines.push(current_line))
    } else {
        parse_input_helper(input, i + 1, current_line.push(input[i]), lines)
    }
}

spec fn parse_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if !('0' <= s[0] <= '9') {
        0
    } else {
        (s[0] as int - '0' as int) + 10 * parse_int(s.skip(1))
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if !('0' <= s[0] <= '9') {
        string_to_int(s.skip(1))
    } else {
        (s[0] as int - '0' as int) * pow(10, (s.len() - 1) as nat) + string_to_int(s.skip(1))
    }
}

spec fn pow(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: String) -> (result: String)
    requires
        stdin_input@.len() > 0,
        (exists|i: int| 0 <= i < stdin_input@.len() && stdin_input@[i] == '\n'),
    ensures
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        ({
            let lines = parse_input(stdin_input@);
            if lines.len() >= 2 {
                let n = parse_int(lines[0]);
                let digits = lines[1];
                if valid_input(n, digits) {
                    let min_result = result@.take(result@.len() - 1);
                    min_result.len() == n &&
                    (forall|i: int| 0 <= i < min_result.len() ==> #[trigger] min_result[i] >= '0' && #[trigger] min_result[i] <= '9') &&
                    (exists|index: int| 0 <= index < n && min_result == modify_string(digits, index)) &&
                    (forall|index: int| 0 <= index < n ==> string_to_int(min_result) <= string_to_int(modify_string(digits, index)))
                } else {
                    result@ == seq!['\n']
                }
            } else {
                result@ == seq!['\n']
            }
        })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}