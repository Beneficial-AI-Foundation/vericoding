use vstd::prelude::*;

verus! {

// <vc-helpers>
// Added helper lemma to relate (forall k < i+1) to (forall k < i) && P(i)
fn forall_extend(text: &str, n: int, i: int)
    requires 0 <= i && i < n && text@.len() == n
    ensures (forall|k: int| 0 <= k < i + 1 ==> #[trigger] text@[k] == text@[n - 1 - k]) ==
            ((forall|k: int| 0 <= k < i ==> #[trigger] text@[k] == text@[n - 1 - k]) && text@[i] == text@[n - 1 - i])
{
    proof {
        // ( (forall k<i) && P(i) ) ==> forall k<i+1. P(k)
        assert(((forall|k: int| 0 <= k < i ==> #[trigger] text@[k] == text@[n - 1 - k]) && text@[i] == text@[n - 1 - i]) 
               ==> (forall|k: int| 0 <= k < i + 1 ==> #[trigger] text@[k] == text@[n - 1 - k]));
        // forall k<i+1. P(k) ==> (forall k<i) && P(i)
        assert((forall|k: int| 0 <= k < i + 1 ==> #[trigger] text@[k] == text@[n - 1 - k]) 
               ==> ((forall|k: int| 0 <= k < i ==> #[trigger] text@[k] == text@[n - 1 - k]) && text@[i] == text@[n - 1 - i]));
    }
}
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
        invariant 0 <= i && i <= n;
        invariant res == (forall|k: int| 0 <= k < i ==> #[trigger] text@[k] == text@[n - 1 - k]);
        decreases n - i;
    {
        let eq: bool = text@[i] == text@[n - 1 - i];
        let new_res: bool = res && eq;
        proof {
            // Use the invariant and eq to show new_res corresponds to forall up to i+1
            assert(res == (forall|k: int| 0 <= k < i ==> #[trigger] text@[k] == text@[n - 1 - k]));
            assert(eq == (text@[i] == text@[n - 1 - i]));
            assert(new_res == res && eq);
            // apply lemma to relate ((forall k<i) && P(i)) with forall k<i+1
            forall_extend(text, n, i);
            // combine equalities to conclude:
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