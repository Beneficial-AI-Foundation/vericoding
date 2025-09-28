// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else if n == 2 { seq!['2'] }
    else if n == 3 { seq!['3'] }
    else if n == 4 { seq!['4'] }
    else if n == 5 { seq!['5'] }
    else if n == 6 { seq!['6'] }
    else if n == 7 { seq!['7'] }
    else if n == 8 { seq!['8'] }
    else if n == 9 { seq!['9'] }
    else if n == 10 { seq!['1', '0'] }
    else if n == 11 { seq!['1', '1'] }
    else if n == 12 { seq!['1', '2'] }
    else if n == 13 { seq!['1', '3'] }
    else if n == 14 { seq!['1', '4'] }
    else if n == 15 { seq!['1', '5'] }
    else if n == 16 { seq!['1', '6'] }
    else if n == 17 { seq!['1', '7'] }
    else if n == 18 { seq!['1', '8'] }
    else if n == 19 { seq!['1', '9'] }
    else if n == 20 { seq!['2', '0'] }
    else if n == 21 { seq!['2', '1'] }
    else if n == 22 { seq!['2', '2'] }
    else if n == 23 { seq!['2', '3'] }
    else { seq!['0'] }
}

spec fn valid_input(input: Seq<char>) -> bool {
    exists|a: int, b: int| 0 <= a <= 23 && 0 <= b <= 23 && 
    (input == int_to_string(a) + seq![' '] + int_to_string(b) + seq!['\n'] ||
     input == int_to_string(a) + seq![' '] + int_to_string(b))
}

spec fn contest_start_time(a: int, b: int) -> int {
    (a + b) % 24
}

spec fn correct_output(input: Seq<char>, result: Seq<char>) -> bool {
    valid_input(input) ==> 
    exists|a: int, b: int| 0 <= a <= 23 && 0 <= b <= 23 && 
    (input == int_to_string(a) + seq![' '] + int_to_string(b) + seq!['\n'] ||
     input == int_to_string(a) + seq![' '] + int_to_string(b)) &&
    result == int_to_string(contest_start_time(a, b)) + seq!['\n']
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed parse_input return type to (i32, i32) for compilability */
pub fn char_to_digit(c: char) -> (result: i32)
    requires
        c.is_ascii_digit(),
    ensures
        0 <= result <= 9,
        result == ((c as u32 - '0' as u32) as i32),
{
    ((c as u32 - '0' as u32) as i32)
}

pub fn string_to_int(s: Seq<char>) -> (result: i32)
    requires
        s.len() == 1 || s.len() == 2,
        forall |i: int| 0 <= i < s.len() ==> s[i].is_ascii_digit(),
    ensures
        if s.len() == 1 { 0 <= result <= 9 } else { 10 <= result <= 23 },
        if s.len() == 1 { result == char_to_digit(s[0]) }
        else { result == 10 * char_to_digit(s[0]) + char_to_digit(s[1]) },
{
    if s.len() == 1 {
        char_to_digit(s[0])
    } else {
        10 * char_to_digit(s[0]) + char_to_digit(s[1])
    }
}

pub fn parse_input(input: Seq<char>) -> (i32, i32)
    requires
        valid_input(input),
    ensures
        0 <= result.0 <= 23,
        0 <= result.1 <= 23,
{
    let mut i = 0;
    let mut space_index = -1;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            space_index == -1 ==> (forall |j: int| 0 <= j < i ==> input[j] != ' '),
            space_index != -1 ==> (space_index >= 0 && space_index < i && input[space_index] == ' '),
        decreases
            input.len() - i,
    {
        if input[i] == ' ' {
            space_index = i;
            break;
        }
        i += 1;
    }
    proof {
        assert(space_index != -1);
    }
    let s1 = input.subrange(0, space_index);
    let rest = input.subrange(space_index + 1, input.len());
    let mut nl_index = -1;
    i = 0;
    while i < rest.len()
        invariant
            0 <= i <= rest.len(),
            nl_index == -1 ==> (forall |j: int| 0 <= j < i ==> rest[j] != '\n'),
            nl_index != -1 ==> (nl_index >= 0 && nl_index < i && rest[nl_index] == '\n'),
        decreases
            rest.len() - i,
    {
        if rest[i] == '\n' {
            nl_index = i;
            break;
        }
        i += 1;
    }
    let s2 = if nl_index == -1 { rest } else { rest.subrange(0, nl_index) };
    let a = string_to_int(s1);
    let b = string_to_int(s2);
    proof {
        assert(0 <= a <= 23);
        assert(0 <= b <= 23);
    }
    (a, b)
}

pub fn int_to_string_exec(n: int) -> Seq<char>
    requires
        0 <= n <= 23,
    ensures
        int_to_string_exec(n) == int_to_string(n),
{
    if n == 0 { seq!['0'] }
    else if n == 1 { seq!['1'] }
    else if n == 2 { seq!['2'] }
    else if n == 3 { seq!['3'] }
    else if n == 4 { seq!['4'] }
    else if n == 5 { seq!['5'] }
    else if n == 6 { seq!['6'] }
    else if n == 7 { seq!['7'] }
    else if n == 8 { seq!['8'] }
    else if n == 9 { seq!['9'] }
    else if n == 10 { seq!['1', '0'] }
    else if n == 11 { seq!['1', '1'] }
    else if n == 12 { seq!['1', '2'] }
    else if n == 13 { seq!['1', '3'] }
    else if n == 14 { seq!['1', '4'] }
    else if n == 15 { seq!['1', '5'] }
    else if n == 16 { seq!['1', '6'] }
    else if n == 17 { seq!['1', '7'] }
    else if n == 18 { seq!['1', '8'] }
    else if n == 19 { seq!['1', '9'] }
    else if n == 20 { seq!['2', '0'] }
    else if n == 21 { seq!['2', '1'] }
    else if n == 22 { seq!['2', '2'] }
    else if n == 23 { seq!['2', '3'] }
    else { seq!['0'] }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    ensures correct_output(input@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): cast time to int for int_to_string_exec argument */
{
    let input_sequence = input@;
    let (a, b) = parse_input(input_sequence);
    let time = ((a + b) % 24) as int;
    let output_sequence = int_to_string_exec(time) + seq!['\n'];
    let output_vec: Vec<char> = output_sequence.collect();
    String::from(output_vec)
}
// </vc-code>


}

fn main() {}