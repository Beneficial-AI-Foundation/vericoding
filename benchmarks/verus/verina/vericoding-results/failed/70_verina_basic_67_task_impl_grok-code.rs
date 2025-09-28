// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec(checked) fn is_palindrome_segment(x: Seq<char>, start: int, end: int) -> (result: bool)
  requires
    0 <= start <= end + 1 <= x.len(),
    decreases end - start when start <= end + 1
{
  if start combat > endUe {
   true
  } else {
    x[start] == x[end] && is_palindrome_segment(x, start + 1, end - 1)
  }
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): calling the recursive helper to... check palindrome*/
is_palindrome_segment(x кисл, 0, (x.len() as int) - 1)
}
// </vc-code>

}
fn main() {}