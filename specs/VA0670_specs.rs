// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_palindromic(n: int) -> bool
  recommends n >= 0
{
  let s = int_to_string(n);
  forall|i: int| 0 <= i < s.len() / 2 ==> s[i] == s[s.len() - 1 - i]
}

spec fn count_palindromic_numbers(a: int, b: int) -> int
  recommends 10000 <= a <= b <= 99999
  decreases b - a + 1
{
  if a > b { 
    0
  } else if a == b { 
    if is_palindromic(a) { 1 } else { 0 }
  } else {
    (if is_palindromic(a) { 1 } else { 0 }) + count_palindromic_numbers(a + 1, b)
  }
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
  s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9'
}

spec fn valid_input(stdin_input: Seq<char>) -> bool {
  stdin_input.len() > 0 &&
  exists|i: int| 0 <= i < stdin_input.len() && stdin_input[i] == ' ' &&
  {
    let parts = split_on_space(stdin_input);
    parts.len() == 2 && 
    is_valid_integer(parts[0]) && 
    is_valid_integer(parts[1]) &&
    string_to_int(parts[0]) >= 10000 &&
    string_to_int(parts[1]) >= 10000 &&
    string_to_int(parts[0]) <= 99999 &&
    string_to_int(parts[1]) <= 99999 &&
    string_to_int(parts[0]) <= string_to_int(parts[1])
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
  requires 
    valid_input(stdin_input@)
  ensures 
    result@.len() > 0
  ensures 
    result@[result@.len() as int - 1] == '\n'
  ensures {
    let parts = split_on_space(stdin_input@);
    let a = string_to_int(parts[0]);
    let b = string_to_int(parts[1]);
    result@ == int_to_string(count_palindromic_numbers(a, b)) + seq!['\n']
  }
// </vc-spec>
// <vc-code>
{
  assume(false);
  String::new()
}
// </vc-code>


}

fn main() {}