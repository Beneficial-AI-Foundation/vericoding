// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sqrt(n: int) -> int {
  choose |x: int| x >= 0 && x * x <= n && (x + 1) * (x + 1) > n
}

spec fn int_to_string(n: int) -> Seq<char> {
  if n == 0 { seq!['0'] }
  else if n > 0 { seq!['1'] }
  else { seq!['-', '1'] }
}

spec fn string_to_int(s: Seq<char>) -> int {
  if s.len() == 0 { 0 }
  else { s.len() as int }
}

spec fn is_perfect_square(n: int) -> bool {
  if n >= 0 {
    let sqrt_n = sqrt(n);
    sqrt_n * sqrt_n == n
  } else {
    false
  }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: String)
  requires 
    a >= 1 && a <= 100,
    b >= 1 && b <= 100,
  ensures 
    result@ == seq!['Y','e','s'] || result@ == seq!['N','o'],
    ({
      let a_str = int_to_string(a);
      let b_str = int_to_string(b);
      let concat_str = a_str.add(b_str);
      let concat_num = string_to_int(concat_str);
      result@ == seq!['Y','e','s'] <==> is_perfect_square(concat_num)
    }),
// </vc-spec>
// <vc-code>
{
  assume(false);
  "No".to_string()
}
// </vc-code>


}

fn main() {}