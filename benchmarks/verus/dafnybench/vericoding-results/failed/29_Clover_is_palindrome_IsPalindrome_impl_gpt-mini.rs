use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
  ensures result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - i - 1])
// </vc-spec>
// <vc-code>
{
    let n: int = x.len();
    let mut i: int = 0;
    let mut ok: bool = true;
    while i < n
        invariant 0 <= i && i <= n;
        invariant ok == (forall |j: int| 0 <= j < i ==> #[trigger] x@[j] == x@[n - j - 1]);
        decreases n - i;
    {
        if x@[i] != x@[n - i - 1] {
            ok = false;
        }
        i = i + 1;
    }
    ok
}
// </vc-code>

fn main() {}

}