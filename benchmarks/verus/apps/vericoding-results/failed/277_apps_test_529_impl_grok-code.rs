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
/* helper modified by LLM (iteration 5): fixed type issues in spec by using int casts */
fn to_lowercase_exec(c: char) -> (r: char)
    ensures r == to_lowercase(c)
{
    if 'A' <= c && c <= 'Z' {
        ((c as u8) - ('A' as u8) + ('a' as u8)) as char
    } else {
        c
    }
}

fn get_comparison_char_exec(n: i32) -> (r: char)
    requires
        0 <= n <= 26,
    ensures
        r == get_comparison_char(n as int),
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

fn to_uppercase_exec(c: char) -> (r: char)
    ensures r == to_uppercase(c)
{
    if 'a' <= c && c <= 'z' {
        ((c as u8) - ('a' as u8) + ('A' as u8)) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, n: i8) -> (result: Vec<char>)
  requires valid_input(s@, n as int)
  ensures result@ == transform_string(s@, n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches by casting i to int in subrange calls */
    let mut lower = Vec::new();
    let mut i = 0usize;
    while i < s.len()
        invariant
            0 <= i as int <= s@.len(),
            lower@ == to_lowercase_string(s@.subrange(0, i as int)),
        decreases s@.len() - i as int
    {
        lower.push(to_lowercase_exec(s[i]));
        i += 1;
    }
    let cc = get_comparison_char_exec(n as i32);
    let mut result = Vec::new();
    i = 0;
    while i < lower.len()
        invariant
            0 <= i as int <= lower@.len(),
            result@ == transform_with_comp_char(lower@.subrange(0, i as int), cc),
        decreases lower@.len() - i as int
    {
        if lower[i] < cc {
            result.push(to_uppercase_exec(lower[i]));
        } else {
            result.push(lower[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}