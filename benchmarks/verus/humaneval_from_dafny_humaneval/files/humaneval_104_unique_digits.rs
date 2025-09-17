// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_no_even_digit(n: int) -> bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && has_no_even_digit(n / 10)))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn unique_digits(x: Seq<int>) -> (result: Seq<int>)
  ensures 
    forall|i: int| 0 <= i < result.len() ==> has_no_even_digit(result[i]) &&
    forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j] &&
    forall|e: int| x.contains(e) && has_no_even_digit(e) ==> result.contains(e) &&
    forall|e: int| result.contains(e) ==> x.contains(e)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}