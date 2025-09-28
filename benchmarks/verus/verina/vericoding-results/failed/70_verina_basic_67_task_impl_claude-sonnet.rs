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
{
    /* code modified by LLM (iteration 5): Fixed ghost type usage in executable code by using only usize in array indexing */
    let len = x.len();
    if len <= 1 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < (len / 2) as usize
        invariant
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> x[j] == x[len - 1 - j],
    {
        if x[i] != x[(len - 1 - i) as usize] {
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert forall|k: int| 0 <= k < len implies x[k] == x[len - 1 - k] by {
            if k < len / 2 {
                assert(x[k] == x[len - 1 - k]);
            } else if k >= len / 2 {
                let mirror_k = len - 1 - k;
                assert(0 <= mirror_k < len / 2);
                assert(x[mirror_k] == x[len - 1 - mirror_k]);
                assert(x[k] == x[len - 1 - k]);
            }
        };
    }
    
    true
}
// </vc-code>

}
fn main() {}