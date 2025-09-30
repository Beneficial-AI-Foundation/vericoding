// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
  n >= 1
}

spec fn valid_output(s: &Seq<char>, n: int) -> bool {
  s.len() == n &&
  (forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 'a' || s[i] == 'b' || s[i] == 'c') &&
  (forall|i: int| 0 <= i <= s.len() - 3 ==> !(#[trigger] s[i] == s[i+2]))
}

spec fn minimal_c_usage(s: &Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 'a' || s[i] == 'b'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
  requires 
    valid_input(n as int)
  ensures 
    valid_output(&result@, n as int) &&
    minimal_c_usage(&result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed trigger for quantifier in invariant */
{
  let mut result = Vec::new();
  let mut i: i8 = 0;
  while i < n
      invariant
          0 <= i as int <= n as int,
          result.len() == i as int,
          forall|j: int| 0 <= j < i as int ==> 
              (result@[j] == 'a' || result@[j] == 'b') &&
              (result@[j] == if (j % 4 == 0 || j % 4 == 1) { 'a' } else { 'b' }),
          forall|j: int| 0 <= j <= i as int - 3 ==> !(#[trigger] result@[j] == result@[j+2])
      decreases n as int - i as int
  {
      let c = if (i % 4 == 0 || i % 4 == 1) { 'a' } else { 'b' };
      result.push(c);
      if i >= 2 {
          let prev_index = i - 2;
          let expected_prev = if (prev_index % 4 == 0 || prev_index % 4 == 1) { 'a' } else { 'b' };
          if (i % 4 == 0 || i % 4 == 1) {
              assert(expected_prev == 'b');
              assert(c == 'a');
              assert(expected_prev != c);
          } else {
              assert(expected_prev == 'a');
              assert(c == 'b');
              assert(expected_prev != c);
          }
      }
      i += 1;
  }
  result
}
// </vc-code>


}

fn main() {}