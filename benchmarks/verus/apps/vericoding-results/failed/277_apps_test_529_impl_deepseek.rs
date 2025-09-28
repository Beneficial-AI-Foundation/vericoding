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

proof fn lemma_to_lowercase_string_recursive(s: Seq<char>) 
    ensures to_lowercase_string(s).len() == s.len()
    decreases s.len()
{
    if s.len() > 0 {
        lemma_to_lowercase_string_recursive(s.skip(1));
    }
}

proof fn lemma_transform_with_comp_char_len(s: Seq<char>, comp_char: char)
    ensures transform_with_comp_char(s, comp_char).len() == s.len()
    decreases s.len()
{
    if s.len() > 0 {
        lemma_transform_with_comp_char_len(s.skip(1), comp_char);
    }
}

proof fn lemma_transform_string_len(s: Seq<char>, n: int)
    requires valid_input(s, n)
    ensures transform_string(s, n).len() == s.len()
{
    lemma_to_lowercase_string_recursive(s);
    lemma_transform_with_comp_char_len(to_lowercase_string(s), get_comparison_char(n));
}

fn to_lowercase_char(c: char) -> (r: char)
    ensures r == to_lowercase(c)
{
    if c >= 'A' && c <= 'Z' {
        ((c as u8) - ('A' as u8) + ('a' as u8)) as char
    } else {
        c
    }
}

fn to_uppercase_char(c: char) -> (r: char)
    ensures r == to_uppercase(c)
{
    if c >= 'a' && c <= 'z' {
        ((c as u8) - ('a' as u8) + ('A' as u8)) as char
    } else {
        c
    }
}

fn get_comparison_char_concrete(n: i8) -> (r: char)
    requires 0 <= n <= 26
    ensures r == get_comparison_char(n as int)
{
    match n {
        0 => 'a',
        1 => 'b',
        2 => 'c',
        3 => 'd',
        4 => 'e',
        5 => 'f',
        6 => 'g',
        7 => 'h',
        8 => 'i',
        9 => 'j',
        10 => 'k',
        11 => 'l',
        12 => 'm',
        13 => 'n',
        14 => 'o',
        15 => 'p',
        16 => 'q',
        17 => 'r',
        18 => 's',
        19 => 't',
        20 => 'u',
        21 => 'v',
        22 => 'w',
        23 => 'x',
        24 => 'y',
        25 => 'z',
        _ => '|',
    }
}

proof fn lemma_transform_with_comp_char_prop(s: Seq<char>, comp_char: char, i: int)
    requires 0 <= i <= s.len()
    ensures transform_with_comp_char(to_lowercase_string(s), comp_char) ==
           transform_with_comp_char(to_lowercase_string(s.subrange(0, i)), comp_char) +
           transform_with_comp_char(to_lowercase_string(s.subrange(i, s.len())), comp_char)
    decreases s.len() - i
{
    if i < s.len() {
        let c = s[i];
        let lower_c = to_lowercase(c);
        let transformed_char = if lower_c < comp_char { to_uppercase(lower_c) } else { lower_c };
        lemma_transform_with_comp_char_prop(s.skip(1), comp_char, i);
    }
}

/* helper modified by LLM (iteration 5): removed lemma_empty_sequence_helper as it's no longer needed */

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, n: i8) -> (result: Vec<char>)
  requires valid_input(s@, n as int)
  ensures result@ == transform_string(s@, n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed subrange calls to use int indices and avoid Seq::empty generics */
    let comp_char = get_comparison_char_concrete(n);
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result@ == transform_with_comp_char(to_lowercase_string(s@.subrange(0, i as int)), comp_char),
        decreases s.len() - i
    {
        let lower_c = to_lowercase_char(s[i]);
        if lower_c < comp_char {
            let upper_c = to_uppercase_char(lower_c);
            result.push(upper_c);
        } else {
            result.push(s[i]);
        }
        i += 1;
        
        proof {
            lemma_to_lowercase_string_recursive(s@.subrange(0, i as int));
        }
    }
    
    proof {
        lemma_to_lowercase_string_recursive(s@);
        lemma_transform_with_comp_char_prop(s@, comp_char, s.len() as int);
        assert(result@ == transform_with_comp_char(to_lowercase_string(s@.subrange(0, s.len() as int)), comp_char));
        assert(to_lowercase_string(s@.subrange(s.len() as int, s.len() as int)).len() == 0);
        assert(transform_with_comp_char(to_lowercase_string(s@.subrange(s.len() as int, s.len() as int)), comp_char) == Seq::empty());
        assert(transform_string(s@, n as int) == transform_with_comp_char(to_lowercase_string(s@), comp_char));
    }
    
    result
}
// </vc-code>


}

fn main() {}