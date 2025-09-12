// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, digits: Seq<u8>) -> bool {
    n > 0 && digits.len() == n && forall|i: int| 0 <= i < digits.len() ==> ('0' as u8) <= digits[i] <= ('9' as u8)
}

spec fn modify_string(s: Seq<u8>, index: int) -> Seq<u8>
    recommends 0 <= index < s.len(),
               forall|i: int| 0 <= i < s.len() ==> ('0' as u8) <= s[i] <= ('9' as u8)
{
    let key = if s[index] == ('0' as u8) { 0 } else { 10 - (s[index] - ('0' as u8)) as int };
    let transformed = transform_digits(s, key);
    rotate_string(transformed, index)
}

spec fn transform_digits(s: Seq<u8>, key: int) -> Seq<u8>
    recommends forall|i: int| 0 <= i < s.len() ==> ('0' as u8) <= s[i] <= ('9' as u8),
               0 <= key <= 9
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let digit = ((s[0] - ('0' as u8)) as int + key) % 10;
        let result_tail = transform_digits(s.subrange(1, s.len() as int), key);
        seq![('0' as u8) + digit as u8].add(result_tail)
    }
}

spec fn rotate_string(s: Seq<u8>, index: int) -> Seq<u8>
    recommends 0 <= index < s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        s.subrange(index, s.len() as int).add(s.subrange(0, index))
    }
}

spec fn is_all_digits(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> ('0' as u8) <= s[i] <= ('9' as u8)
}

spec fn parse_input(input: Seq<u8>) -> Seq<Seq<u8>>
    decreases input.len()
{
    parse_input_helper(input, 0, seq![], seq![])
}

spec fn parse_input_helper(input: Seq<u8>, i: int, current_line: Seq<u8>, lines: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    recommends 0 <= i <= input.len()
    decreases input.len() - i
{
    if i >= input.len() {
        if current_line.len() > 0 { lines.push(current_line) } else { lines }
    } else if input[i] == ('\n' as u8) {
        parse_input_helper(input, i + 1, seq![], lines.push(current_line))
    } else {
        parse_input_helper(input, i + 1, current_line.push(input[i]), lines)
    }
}

spec fn parse_int(s: Seq<u8>) -> int {
    if s.len() == 0 {
        0
    } else if !(('0' as u8) <= s[0] <= ('9' as u8)) {
        0
    } else {
        (s[0] - ('0' as u8)) as int + 10 * parse_int(s.subrange(1, s.len() as int))
    }
}

spec fn seq_to_int(s: Seq<u8>) -> int {
    if s.len() == 0 {
        0
    } else {
        seq_to_int(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] - ('0' as u8)) as int
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires stdin_input.len() > 0,
             exists|i: int| 0 <= i < stdin_input.len() && stdin_input.as_bytes()[i] == ('\n' as u8)
    ensures result.len() > 0,
            result.as_bytes()[result.len() - 1] == ('\n' as u8),
            ({
                let lines = parse_input(stdin_input.as_bytes()@);
                if lines.len() >= 2 {
                    let n = parse_int(lines[0]);
                    let digits = lines[1];
                    if valid_input(n, digits) {
                        let min_result = result.as_bytes()@.subrange(0, result.len() - 1);
                        min_result.len() == n &&
                        (forall|i: int| 0 <= i < min_result.len() ==> ('0' as u8) <= min_result[i] <= ('9' as u8)) &&
                        (exists|index: int| 0 <= index < n && min_result == modify_string(digits, index)) &&
                        (forall|index: int| 0 <= index < n ==> seq_to_int(min_result) <= seq_to_int(modify_string(digits, index)))
                    } else {
                        result == "\n"
                    }
                } else {
                    result == "\n"
                }
            })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    String::new()
    // impl-end
}
// </vc-code>


}

fn main() {}