// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(lst: Seq<int>) -> bool {
  5 <= lst.len() <= 10 &&
  forall|i: int| 0 <= i < lst.len() ==> 1 <= lst[i] <= 32
}

spec fn int_xor(a: int, b: int) -> int {
  let a_bv = a as u32;
  let b_bv = b as u32;
  (a_bv ^ b_bv) as int
}

spec fn min_of_sequence(s: Seq<int>) -> int
  decreases s.len()
{
  if s.len() == 1 { 
    s[0]
  } else if s[0] <= min_of_sequence(s.skip(1)) { 
    s[0]
  } else { 
    min_of_sequence(s.skip(1))
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(lst: Seq<int>) -> (result: int)
  requires valid_input(lst)
  ensures result == 2 + int_xor(lst[2], min_of_sequence(lst))
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}