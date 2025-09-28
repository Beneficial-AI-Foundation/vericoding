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
#[verifier::spinoff_prover]
proof fn lemma_to_lowercase_string_append(s1: Seq<char>, s2: Seq<char>)
    ensures to_lowercase_string(s1 + s2) == to_lowercase_string(s1) + to_lowercase_string(s2)
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_to_lowercase_string_append(s1.skip(1), s2);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_transform_with_comp_char_append(s1: Seq<char>, s2: Seq<char>, comp_char: char)
    ensures transform_with_comp_char(s1 + s2, comp_char) == transform_with_comp_char(s1, comp_char) + transform_with_comp_char(s2, comp_char)
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_transform_with_comp_char_append(s1.skip(1), s2, comp_char);
    }
}

fn get_comparison_char_exec(n: i8) -> (c: char)
    requires 0 <= n <= 26
    ensures c == get_comparison_char(n as int)
{
    if n == 26 {
        '|'
    } else {
        assert(get_comparison_char(n as int) == (('a' as u8) + (n as u8)) as char);
        (('a' as u8) + n as u8) as char
    }
}

fn to_lowercase_exec(c: char) -> (res: char)
    ensures res == to_lowercase(c)
{
    if 'A' <= c && c <= 'Z' {
        ((c as u8) - ('A' as u8) + ('a' as u8)) as char
    } else {
        c
    }
}

fn to_uppercase_exec(c: char) -> (res: char)
    ensures res == to_uppercase(c)
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
    let comp_char = get_comparison_char_exec(n);

    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            comp_char == get_comparison_char(n as int),
            result@ == transform_string(s@.subrange(0, i as int), n as int),
        decreases s.len() - i
    {
        proof {
            let s_prefix = s@.subrange(0, i as int);
            let next_char_seq = seq![s@[i as int]];
            lemma_to_lowercase_string_append(s_prefix, next_char_seq);
            lemma_transform_with_comp_char_append(
                to_lowercase_string(s_prefix),
                to_lowercase_string(next_char_seq),
                comp_char
            );
        }

        let current_char = s[i];
        let lower_char = to_lowercase_exec(current_char);

        let transformed_char = if lower_char < comp_char {
            to_uppercase_exec(lower_char)
        } else {
            lower_char
        };
        
        result.push(transformed_char);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}