use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: int = text@.len();
    let mut i: int = 0;
    let mut res: bool = true;
    while i < n
        invariant 0 <= i <= n
        invariant res == forall|k: int| 0 <= k < i ==> #[trigger] text@[k] == text@[n - 1 - k]
    {
        let eq: bool = text@[i] == text@[n - 1 - i];
        let new_res: bool = res && eq;
        proof {
            // res == forall k < i. P(k)
            assert(res == forall|k: int| 0 <= k < i ==> #[trigger] text@[k] == text@[n - 1 - k]);
            // eq == P(i)
            assert(eq == (text@[i] == text@[n - 1 - i]));
            // combine to get new_res == forall k < i+1. P(k)
            assert(new_res == (forall|k: int| 0 <= k < i + 1 ==> #[trigger] text@[k] == text@[n - 1 - k]));
        }
        res = new_res;
        i = i + 1;
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}