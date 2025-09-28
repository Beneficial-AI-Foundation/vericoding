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

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, n: i8) -> (result: Vec<char>)
  requires valid_input(s@, n as int)
  ensures result@ == transform_string(s@, n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let comp_char = if n == 0 { 'a' as char }
        else if n == 1 { 'b' as char }
        else if n == 2 { 'c' as char }
        else if n == 3 { 'd' as char }
        else if n == 4 { 'e' as char }
        else if n == 5 { 'f' as char }
        else if n == 6 { 'g' as char }
        else if n == 7 { 'h' as char }
        else if n == 8 { 'i' as char }
        else if n == 9 { 'j' as char }
        else if n == 10 { 'k' as char }
        else if n == 11 { 'l' as char }
        else if n == 12 { 'm' as char }
        else if n == 13 { 'n' as char }
        else if n == 14 { 'o' as char }
        else if n == 15 { 'p' as char }
        else if n == 16 { 'q' as char }
        else if n == 17 { 'r' as char }
        else if n == 18 { 's' as char }
        else if n == 19 { 't' as char }
        else if n == 20 { 'u' as char }
        else if n == 21 { 'v' as char }
        else if n == 22 { 'w' as char }
        else if n == 23 { 'x' as char }
        else if n == 24 { 'y' as char }
        else if n == 25 { 'z' as char }
        else { '|' as char };

    let mut result = Vec::new();
    let mut i: usize = 0;

    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == transform_string(s@, n as int)[j],
        decreases s.len() - i
    {
        let c = s[i];
        let lower_c = if 'A' as char <= c && c <= 'Z' as char {
            ((c as u8) - ('A' as u8) + ('a' as u8)) as char
        } else {
            c
        };
        
        let transformed = if lower_c < comp_char {
            if 'a' as char <= lower_c && lower_c <= 'z' as char {
                ((lower_c as u8) - ('a' as u8) + ('A' as u8)) as char
            } else {
                lower_c
            }
        } else {
            lower_c
        };
        
        result.push(transformed);
        i = i + 1;
    }

    result
}
// </vc-code>


}

fn main() {}