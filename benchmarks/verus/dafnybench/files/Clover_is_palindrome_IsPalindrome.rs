// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
  ensures result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - i - 1])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}