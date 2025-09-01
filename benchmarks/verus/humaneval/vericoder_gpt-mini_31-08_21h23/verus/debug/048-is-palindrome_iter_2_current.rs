use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper functions needed for this example
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
        invariant ok == forall|k: int| 0 <= k < i as int ==> #[trigger] s@[k as nat] == s@[(n - 1 - (k as nat))];
    {
        if s@[i] != s@[(n - 1 - i)] {
            // we found a counterexample at index i, so the universal property over 0..n fails
            proof {
                let kint: int = i as int;
                // 0 <= kint < n
                assert(0 <= kint);
                assert(kint < n as int);
                // s@[i] != s@[(n - 1 - i)], so the forall for range 0..n is false
                assert(s@[i] != s@[(n - 1 - i)]);
            }
            ok = false;
            i = n;
        } else {
            // extend the forall from range 0..i to 0..i+1 using equality at i
            proof {
                // From the invariant we have: ok == forall k < i ==> ...
                assert(ok == forall|k: int| 0 <= k < i as int ==> #[trigger] s@[k as nat] == s@[(n - 1 - (k as nat))]);
                // And we know s@[i] == s@[(n - 1 - i)]
                assert(s@[i] == s@[(n - 1 - i)]);
                // Therefore ok == forall k < i+1 ==> ...
            }
            i = i + 1;
        }
    }

    ok
}
// </vc-code>

fn main() {}
}