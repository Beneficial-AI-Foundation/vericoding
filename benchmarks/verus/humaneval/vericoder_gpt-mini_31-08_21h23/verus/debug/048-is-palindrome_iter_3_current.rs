use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// No helper functions needed for this example
// </vc-helpers>
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
    let s: Seq<char> = text@;
    let n: nat = s.len();

    let mut i: nat = 0;
    let mut ok: bool = true;

    while i < n
        invariant i <= n;
        invariant ok == (forall|k: int| 0 <= k && k < (i as int) ==> #[trigger] s@[k as nat] == s@[(n - 1 - (k as nat))]);
        decreases n - i;
    {
        if s@[i] != s@[(n - 1 - i)] {
            proof {
                let kint: int = i as int;
                assert(0 <= kint);
                assert(kint < n as int);
                assert(s@[i] != s@[(n - 1 - i)]);
            }
            ok = false;
            i = n;
        } else {
            proof {
                // From the loop condition, when entering this branch we have ok == forall(.. < i)
                // and s@[i] == s@[(n - 1 - i)]. We need to show that after incrementing i,
                // ok still equals the forall up to the new i. This follows by case analysis
                // on an arbitrary k: if k < i then use the previous forall, otherwise k == i use the equality.
                assert(ok == (forall|k: int| 0 <= k && k < (i as int) ==> #[trigger] s@[k as nat] == s@[(n - 1 - (k as nat))]));
                assert(s@[i] == s@[(n - 1 - i)]);
                // The detailed universal introduction is handled implicitly by Verus here.
            }
            i = i + 1;
        }
    }

    ok
}
// </vc-code>

fn main() {}
}