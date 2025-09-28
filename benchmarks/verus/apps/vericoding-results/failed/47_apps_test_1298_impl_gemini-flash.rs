// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i] == '0' || #[trigger] s[i] == '1')
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && (s[0] != '0' || s.len() == 1) && forall|i: int| 0 <= i < s.len() ==> ('0' <= #[trigger] s[i] <= '9')
}

spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else { (if s[0] == c { 1int } else { 0int }) + count_char(s.subrange(1, s.len() as int), c) }
}

spec fn abs_diff_count(s: Seq<char>) -> int
    recommends is_binary_string(s)
{
    let count0 = count_char(s, '0');
    let count1 = count_char(s, '1');
    if count1 >= count0 { count1 - count0 } else { count0 - count1 }
}

spec fn int_to_string(n: int) -> Seq<char>
    recommends n >= 0
    decreases n
{
    if n == 0 { seq!['0'] }
    else if n < 10 { seq![char_of_digit(n)] }
    else { int_to_string(n / 10).add(seq![char_of_digit(n % 10)]) }
}

spec fn char_of_digit(d: int) -> char
    recommends 0 <= d <= 9
{
    if d == 0int { '0' }
    else if d == 1int { '1' }
    else if d == 2int { '2' }
    else if d == 3int { '3' }
    else if d == 4int { '4' }
    else if d == 5int { '5' }
    else if d == 6int { '6' }
    else if d == 7int { '7' }
    else if d == 8int { '8' }
    else if d == 9int { '9' }
    else { '0' }
}

spec fn string_to_int(s: Seq<char>) -> int
    recommends is_valid_integer(s)
    decreases s.len()
{
    if s.len() == 0 { 0int }
    else if s.len() == 1 { (s[0] as int) - ('0' as int) }
    else { string_to_int(s.subrange(0, s.len() - 1)) * 10int + ((s[s.len() - 1] as int) - ('0' as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed unnecessary helper, as the error was within the main `solve` function.*/
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires 
        stdin_input@.len() > 0,
        exists|i: int| 0 <= i < stdin_input@.len() && stdin_input@[i] == '\n',
        exists|newline_pos: int| {
            0 <= newline_pos < stdin_input@.len() && stdin_input@[newline_pos] == '\n' &&
            newline_pos + 1 < stdin_input@.len() &&
            exists|binary_end: int| {
                newline_pos + 1 <= binary_end <= stdin_input@.len() &&
                (binary_end == stdin_input@.len() || stdin_input@[binary_end] == '\n') &&
                is_valid_integer(stdin_input@.subrange(0, newline_pos)) &&
                is_binary_string(stdin_input@.subrange(newline_pos + 1, binary_end))
            }
        },
    ensures 
        result@.len() > 0,
        result@[result@.len() - 1] == '\n',
        exists|newline_pos: int| {
            0 <= newline_pos < stdin_input@.len() && stdin_input@[newline_pos] == '\n' &&
            newline_pos + 1 < stdin_input@.len() &&
            exists|binary_end: int| {
                newline_pos + 1 <= binary_end <= stdin_input@.len() &&
                (binary_end == stdin_input@.len() || stdin_input@[binary_end] == '\n') &&
                is_binary_string(stdin_input@.subrange(newline_pos + 1, binary_end)) &&
                result@ == int_to_string(abs_diff_count(stdin_input@.subrange(newline_pos + 1, binary_end))).add(seq!['\n'])
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed compilation errors related to `nat`/`int` types in `exec` contexts by replacing them with `usize`. Added explicit type conversions where necessary to satisfy type checker. Also replaced `as int` with `as usize` for length checks.*/
    let s_input = stdin_input@;
    let mut newline_pos: usize = 0;
    while newline_pos < s_input.len()
        invariant
            0 <= newline_pos && newline_pos <= s_input.len(),
            forall|j: int| 0 <= j < newline_pos as int ==> s_input@[j] != '\n',
    {
        if s_input@[newline_pos as int] == '\n' {
            break;
        }
        newline_pos = newline_pos + 1;
    }

    let mut binary_end: usize = newline_pos + 1;
    while binary_end < s_input.len()
        invariant
            newline_pos < binary_end && binary_end <= s_input.len(),
            forall|j: int| newline_pos as int + 1 <= j && j < binary_end as int ==> s_input@[j] != '\n',
    {
        if s_input@[binary_end as int] == '\n' {
            break;
        }
        binary_end = binary_end + 1;
    }

    let binary_string = s_input.subrange(newline_pos as int + 1, binary_end as int);
    proof {
        assert(is_binary_string(binary_string));
    }

    let diff = abs_diff_count(binary_string);
    let diff_str_seq = int_to_string(diff);
    let result_seq = diff_str_seq.add(seq!['\n']);

    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    while i < result_seq.len()
        invariant {
            0 <= i && i <= result_seq.len(),
            result_vec@.len() == i as nat,
            result_vec@.subrange(0, i as int) == result_seq.subrange(0, i as int),
        }
    {
        result_vec.push(result_seq@[i as int]);
        i = i + 1;
    }

    result_vec
}
// </vc-code>


}
fn main() {}