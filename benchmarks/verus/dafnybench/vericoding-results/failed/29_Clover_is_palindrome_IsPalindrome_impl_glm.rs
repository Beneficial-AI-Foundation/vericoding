use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
  ensures result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - i - 1])
// </vc-spec>
// <vc-code>
{
  if x.len() == 0 {
    true
  } else {
    let mut i: int = 0;
    let n = x.len();
    while (i < n / 2)
      invariant 0 <= i <= n / 2
      invariant (forall|k: int| 0 <= k < i ==> x[k] == x[n - k - 1])
    {
      if x[i] != x[n - i - 1] {
        return false;
      }
      i = i + 1;
    }
    true
  }
}
// </vc-code>

fn main() {}

}