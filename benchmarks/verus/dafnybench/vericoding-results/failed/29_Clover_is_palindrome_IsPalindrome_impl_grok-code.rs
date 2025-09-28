use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed in helpers
// </vc-helpers>

// <vc-spec>
fn is_palindrome(x: Seq<char>) -> (result: bool)
  ensures result <==> (forall|i: int| 0 <= i < x.len() ==> #[trigger] x[i] == x[x.len() - i - 1])
// </vc-spec>
// <vc-code>
{
    let len: usize = x.len();
    let half: usize = len / 2;
    let mut i: usize = 0;
    while i < half
        invariant
            0 <= i <= half,
            forall|k: int| 0 <= k < (i as int) ==> #[trigger] x@[k] == x@[(len as int) - k - 1]
    {
        let idx = (len as int) - (i as int) - 1;
        if x[i] != x[idx as usize] {
            proof {
                assert(!(forall|k: int| 0 <= k < x.len() ==> #[trigger] x@[k] == x@[x.len() - k - 1])) by {
                    assert(x@[i] != x@[(len as int) - (i as int) - 1]);
                }
            }
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

fn main() {}

}