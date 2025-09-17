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
fn solve(n: int) -> (result: Seq<char>)
  requires 
    valid_input(n)
  ensures 
    valid_output(&result, n) &&
    minimal_c_usage(&result)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}