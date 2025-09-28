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
/* helper modified by LLM (iteration 5): no change, already correct */
proof fn find_min_modified_string(init_digits: Seq<char>, n: int) -> (min_res: Seq<char>)
    requires
        n > 0,
        init_digits.len() == n as nat,
        is_all_digits(init_digits),
    ensures
        (exists|idx: int| 0 <= idx < n && min_res == modify_string(init_digits, idx)) &&
        (forall|idx: int| 0 <= idx < n ==> string_to_int(min_res) <= string_to_int(modify_string(init_digits, idx)))
{
    let mut current_min_string = modify_string(init_digits, 0);
    let mut i: int = 1; /* Type annotation for 'i' */

    while i < n
        invariant
            0 <= i <= n,
            init_digits.len() == n as nat,
            is_all_digits(init_digits),
            (exists|idx: int| 0 <= idx < i && current_min_string == modify_string(init_digits, idx)) &&
            (forall|j: int| 0 <= j < i ==> string_to_int(current_min_string) <= string_to_int(modify_string(init_digits, j))),
        decreases n - i
    {
        let next_string = modify_string(init_digits, i);
        if string_to_int(next_string) < string_to_int(current_min_string) {
            current_min_string = next_string;
        }
        i = i + 1;
    }
    current_min_string
}
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
/* code modified by LLM (iteration 5): Corrected type mismatches (nat vs int, Seq::index argument), handled `Seq` to `Vec` conversion for string building. */
{
    let lines = parse_input(stdin_input@);

    if lines.len() < 2 {
        return String::from("\n");
    }

    let n_seq = lines.index(0 as int); 
    let digits_seq = lines.index(1 as int); 

    let n = parse_int(n_seq);

    if !valid_input(n, digits_seq) {
        return String::from("\n");
    }

    // Use the proof function to find the minimum modified string
    let min_modified_spec = find_min_modified_string(digits_seq, n);

    // Now generate the actual string from the solved spec
    let mut result_string_vec = Vec::<char>::new();
    proof {
      assert forall |i: int| 0 <= i < min_modified_spec.len() implies min_modified_spec[i].is_ascii_digit()
        by { assert(min_modified_spec.len() == n as nat); }
    }
    min_modified_spec.to_vec(&mut result_string_vec); // Correct method name is `to_vec`

    result_string_vec.push_back('
'); // Use push_back for single characters in Vec
    String::from_iter(result_string_vec)
}
// </vc-code>


}

fn main() {}