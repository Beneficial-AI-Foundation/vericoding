// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
  100 <= n <= 999
}

spec fn is_palindromic(n: int) -> bool
  recommends valid_input(n)
{
  let hundreds = n / 100;
  let units = n % 10;
  hundreds == units
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
  requires stdin_input@.len() > 0
// </vc-spec>
// <vc-code>
{
  // impl-start
  assume(false);
  "".to_string()
  // impl-end
}
// </vc-code>


}

fn main() {}