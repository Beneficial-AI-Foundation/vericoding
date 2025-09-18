// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - 1 - i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches (nat vs int) in loops and array indexing. */
{
    let len: nat = x.len();
    if len == 0 {
        return true;
    }

    let mut i: nat = 0;
    let mut j: nat = (len - 1) as nat;

    while i < j
        invariant
            0 <= i,
            i <= j + 1,
            j < len,
            forall|k: int| 0 <= k < i ==> (#[trigger] x.index(k) == x.index((len - 1 - k) as int)),
            forall|k: int| j < k < len ==> (#[trigger] x.index(k) == x.index((len - 1 - k) as int)),
        decreases j - i
    {
        proof {
            assert(0 <= i);
            assert(i < len);
            assert(0 <= j);
            assert(j < len);
        }
        if x.index(i as int) != x.index(j as int) {
            return false;
        }
        i = (i + 1) as nat;
        j = (j - 1) as nat;
    }
    true
}
// </vc-code>

}
fn main() {}