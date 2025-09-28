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
/* helper modified by LLM (iteration 2): Renamed exec functions to resolve name conflicts with existing spec functions */
exec fn exec_char_of_digit(d: usize) -> char
    requires
        0 <= d <= 9,
    ensures
        result == char_of_digit(d as int),
{
    match d {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        9 => '9',
        _ => '0'
    }
}

exec fn count_char_in_range(s: &Vec<char>, start: usize, end: usize, c: char) -> nat
    requires
        start <= end <= s.len(),
    ensures
        result == count_char(s@.subrange(start as int, end as int), c),
{
    let mut i = start;
    let mut count = 0;
    while i < end
        invariant
            start <= i <= end,
            count == count_char(s@.subrange(start as int, i as int), c),
        decreases (end - i)
    {
        if s[i] == c {
            count += 1;
        }
        i += 1;
    }
    count
}

exec fn exec_int_to_string(n: usize) -> Vec<char>
    requires
        n >= 0,
    ensures
        result@ == int_to_string(n as int),
    decreases n
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        result
    } else if n < 10 {
        let mut result = Vec::new();
        result.push(exec_char_of_digit(n));
        result
    } else {
        let mut result = exec_int_to_string(n / 10);
        result.push(exec_char_of_digit(n % 10));
        result
    }
}
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
/* code modified by LLM (iteration 2): Updated calls to use renamed exec helper functions */
{
    let mut newline_pos = 0;
    while newline_pos < stdin_input.len() && stdin_input[newline_pos] != '\n'
        invariant
            0 <= newline_pos <= stdin_input.len(),
        decreases (stdin_input.len() - newline_pos)
    {
        newline_pos += 1;
    }
    proof {
        assert(exists|i: int| 0 <= i < stdin_input@.len() && stdin_input@[i] == '\n');
    }
    let binary_start = newline_pos + 1;
    let mut binary_end = binary_start;
    while binary_end < stdin_input.len() && stdin_input[binary_end] != '\n'
        invariant
            binary_start <= binary_end <= stdin_input.len(),
        decreases (stdin_input.len() - binary_end)
    {
        binary_end += 1;
    }
    let count0 = count_char_in_range(&stdin_input, binary_start, binary_end, '0');
    let count1 = count_char_in_range(&stdin_input, binary_start, binary_end, '1');
    let abs_diff = if count1 >= count0 { count1 - count0 } else { count0 - count1 };
    let mut result = exec_int_to_string(abs_diff as usize);
    result.push('\n');
    result
}
// </vc-code>


}
fn main() {}