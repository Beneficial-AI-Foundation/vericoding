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
/* helper modified by LLM (iteration 5): Fixed type mismatch in parse functions */
fn parse_single_digit(c: char) -> (n: Option<usize>)
    ensures
        n.is_some() ==> n.unwrap() <= 9
{
    if c == '0' { Some(0) }
    else if c == '1' { Some(1) }
    else if c == '2' { Some(2) }
    else if c == '3' { Some(3) }
    else if c == '4' { Some(4) }
    else if c == '5' { Some(5) }
    else if c == '6' { Some(6) }
    else if c == '7' { Some(7) }
    else if c == '8' { Some(8) }
    else if c == '9' { Some(9) }
    else { None }
}

fn parse_number_from_chars(chars: &Vec<char>) -> (n: Option<usize>)
    ensures
        n.is_some() ==> n.unwrap() <= 23
{
    if chars.len() == 1 {
        let d = parse_single_digit(chars[0]);
        if d.is_some() {
            Some(d.unwrap())
        } else {
            None
        }
    } else if chars.len() == 2 {
        let d1 = parse_single_digit(chars[0]);
        let d2 = parse_single_digit(chars[1]);
        if d1.is_some() && d2.is_some() {
            let val = d1.unwrap() * 10 + d2.unwrap();
            if val <= 23 {
                Some(val)
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    }
}

fn number_to_string(n: usize) -> (s: String)
    requires
        n <= 23
    ensures
        s@ == int_to_string(n as int)
{
    if n == 0 { "0".to_string() }
    else if n == 1 { "1".to_string() }
    else if n == 2 { "2".to_string() }
    else if n == 3 { "3".to_string() }
    else if n == 4 { "4".to_string() }
    else if n == 5 { "5".to_string() }
    else if n == 6 { "6".to_string() }
    else if n == 7 { "7".to_string() }
    else if n == 8 { "8".to_string() }
    else if n == 9 { "9".to_string() }
    else if n == 10 { "10".to_string() }
    else if n == 11 { "11".to_string() }
    else if n == 12 { "12".to_string() }
    else if n == 13 { "13".to_string() }
    else if n == 14 { "14".to_string() }
    else if n == 15 { "15".to_string() }
    else if n == 16 { "16".to_string() }
    else if n == 17 { "17".to_string() }
    else if n == 18 { "18".to_string() }
    else if n == 19 { "19".to_string() }
    else if n == 20 { "20".to_string() }
    else if n == 21 { "21".to_string() }
    else if n == 22 { "22".to_string() }
    else { "23".to_string() }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    ensures correct_output(input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Create vector manually without using collect() */
    let mut chars: Vec<char> = Vec::new();
    let input_len = input.unicode_len();
    let mut idx: usize = 0;
    while idx < input_len
        invariant
            idx <= input_len,
            chars.len() == idx
    {
        chars.push(input.get_char(idx));
        idx = idx + 1;
    }
    
    // Find space position
    let mut space_pos: Option<usize> = None;
    let mut i: usize = 0;
    while i < chars.len()
        invariant
            i <= chars.len(),
            space_pos.is_none() || (space_pos.unwrap() < i && chars@[space_pos.unwrap() as int] == ' ')
    {
        if chars[i] == ' ' && space_pos.is_none() {
            space_pos = Some(i);
        }
        i = i + 1;
    }
    
    if space_pos.is_none() {
        return "0\n".to_string();
    }
    
    let sp = space_pos.unwrap();
    
    // Extract first number characters
    let mut first_num: Vec<char> = Vec::new();
    let mut j: usize = 0;
    while j < sp
        invariant
            j <= sp,
            sp <= chars.len()
    {
        first_num.push(chars[j]);
        j = j + 1;
    }
    
    // Extract second number characters (skip space)
    let mut second_num: Vec<char> = Vec::new();
    let mut k: usize = sp + 1;
    while k < chars.len() && chars[k] != '\n'
        invariant
            sp + 1 <= k,
            k <= chars.len()
    {
        second_num.push(chars[k]);
        k = k + 1;
    }
    
    let a_opt = parse_number_from_chars(&first_num);
    let b_opt = parse_number_from_chars(&second_num);
    
    if a_opt.is_some() && b_opt.is_some() {
        let a = a_opt.unwrap();
        let b = b_opt.unwrap();
        let sum = (a + b) % 24;
        let result_str = number_to_string(sum);
        return result_str + "\n";
    } else {
        return "0\n".to_string();
    }
}
// </vc-code>


}

fn main() {}