// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn palindrome_from_half(s: Seq<char>)
    requires
        forall|i: int| 0 <= i < s.len() / 2 ==> #[trigger] s[i] == s[s.len() - 1 - i],
    ensures
        forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] == s[s.len() - 1 - j],
{
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
  ensures result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - i - 1])
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    while i < x.len() / 2
        invariant
            0 <= i <= x.len() / 2,
            forall|k: int| 0 <= k < i ==> #[trigger] x[k] == x[x.len() - 1 - k],
        decreases x.len() / 2 - i
    {
        if x[i] != x[x.len() - 1 - i] {
            return false;
        }
        i = i + 1;
    }

    palindrome_from_half(x);

    true
}
// </vc-code>

}
fn main() {}