// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>, n: int) -> bool {
  0 <= n <= 26
}

spec fn get_comparison_char(n: int) -> char {
  if n == 0 { 'a' }
  else if n == 1 { 'b' }
  else if n == 2 { 'c' }
  else if n == 3 { 'd' }
  else if n == 4 { 'e' }
  else if n == 5 { 'f' }
  else if n == 6 { 'g' }
  else if n == 7 { 'h' }
  else if n == 8 { 'i' }
  else if n == 9 { 'j' }
  else if n == 10 { 'k' }
  else if n == 11 { 'l' }
  else if n == 12 { 'm' }
  else if n == 13 { 'n' }
  else if n == 14 { 'o' }
  else if n == 15 { 'p' }
  else if n == 16 { 'q' }
  else if n == 17 { 'r' }
  else if n == 18 { 's' }
  else if n == 19 { 't' }
  else if n == 20 { 'u' }
  else if n == 21 { 'v' }
  else if n == 22 { 'w' }
  else if n == 23 { 'x' }
  else if n == 24 { 'y' }
  else if n == 25 { 'z' }
  else { '|' }
}

spec fn is_lowercase(c: char) -> bool {
  'a' <= c && c <= 'z'
}

spec fn is_uppercase(c: char) -> bool {
  'A' <= c && c <= 'Z'
}

spec fn to_lowercase(c: char) -> char {
  if is_uppercase(c) {
    ((c as u8) - ('A' as u8) + ('a' as u8)) as char
  } else {
    c
  }
}

spec fn to_uppercase(c: char) -> char {
  if is_lowercase(c) {
    ((c as u8) - ('a' as u8) + ('A' as u8)) as char
  } else {
    c
  }
}

spec fn transform_string(s: Seq<char>, n: int) -> Seq<char> {
  let comp_char = get_comparison_char(n);
  transform_with_comp_char(to_lowercase_string(s), comp_char)
}

spec fn to_lowercase_string(s: Seq<char>) -> Seq<char>
  decreases s.len()
{
  if s.len() == 0 {
    s
  } else {
    s.subrange(0, 1).map(|_i: int, c: char| to_lowercase(c)) + to_lowercase_string(s.skip(1))
  }
}

spec fn transform_with_comp_char(s: Seq<char>, comp_char: char) -> Seq<char>
  decreases s.len()
{
  if s.len() == 0 {
    s
  } else if s[0] < comp_char {
    s.subrange(0, 1).map(|_i: int, c: char| to_uppercase(c)) + transform_with_comp_char(s.skip(1), comp_char)
  } else {
    s.subrange(0, 1) + transform_with_comp_char(s.skip(1), comp_char)
  }
}
// </vc-preamble>

// <vc-helpers>
fn exec_get_comparison_char(n: i8) -> (result: char)
    requires 0 <= n as int <= 26
    ensures result == get_comparison_char(n as int)
{
    if n == 0 { 'a' }
    else if n == 1 { 'b' }
    else if n == 2 { 'c' }
    else if n == 3 { 'd' }
    else if n == 4 { 'e' }
    else if n == 5 { 'f' }
    else if n == 6 { 'g' }
    else if n == 7 { 'h' }
    else if n == 8 { 'i' }
    else if n == 9 { 'j' }
    else if n == 10 { 'k' }
    else if n == 11 { 'l' }
    else if n == 12 { 'm' }
    else if n == 13 { 'n' }
    else if n == 14 { 'o' }
    else if n == 15 { 'p' }
    else if n == 16 { 'q' }
    else if n == 17 { 'r' }
    else if n == 18 { 's' }
    else if n == 19 { 't' }
    else if n == 20 { 'u' }
    else if n == 21 { 'v' }
    else if n == 22 { 'w' }
    else if n == 23 { 'x' }
    else if n == 24 { 'y' }
    else if n == 25 { 'z' }
    else { '|' }
}

fn exec_to_lowercase(c: char) -> (result: char)
    ensures result == to_lowercase(c)
{
    if 'A' <= c && c <= 'Z' {
        ((c as u8) - ('A' as u8) + ('a' as u8)) as char
    } else {
        c
    }
}

fn exec_to_uppercase(c: char) -> (result: char)
    ensures result == to_uppercase(c)
{
    if 'a' <= c && c <= 'z' {
        ((c as u8) - ('a' as u8) + ('A' as u8)) as char
    } else {
        c
    }
}

/* helper modified by LLM (iteration 3): added decreases clause for loop termination */
/* helper modified by LLM (iteration 2): fixed type mismatch in invariant by casting usize to int */
fn exec_to_lowercase_string(s: &Vec<char>) -> (result: Vec<char>)
    ensures result@ == to_lowercase_string(s@)
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i as int <= s@.len(),
            result@ == to_lowercase_string(s@.subrange(0, i as int))
        decreases s.len() - i
    {
        result.push(exec_to_lowercase(s[i]));
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 3): added decreases clause for loop termination */
/* helper modified by LLM (iteration 2): fixed type mismatch in invariant by casting usize to int */
fn exec_transform_with_comp_char(s: &Vec<char>, comp_char: char) -> (result: Vec<char>)
    ensures result@ == transform_with_comp_char(s@, comp_char)
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i as int <= s@.len(),
            result@ == transform_with_comp_char(s@.subrange(0, i as int), comp_char)
        decreases s.len() - i
    {
        if s[i] < comp_char {
            result.push(exec_to_uppercase(s[i]));
        } else {
            result.push(s[i]);
        }
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, n: i8) -> (result: Vec<char>)
  requires valid_input(s@, n as int)
  ensures result@ == transform_string(s@, n as int)
// </vc-spec>
// <vc-code>
{
    let comp_char = exec_get_comparison_char(n);
    let lower_s = exec_to_lowercase_string(&s);
    let transformed_s = exec_transform_with_comp_char(&lower_s, comp_char);
    transformed_s
}
// </vc-code>


}

fn main() {}