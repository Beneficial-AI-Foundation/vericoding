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
    /* code modified by LLM (iteration 5): Fixed exec context sequence access without int conversions */
    let n = x.len();
    
    if n == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            n == x.len(),
            forall|j: int| 0 <= j < i as int ==> x[j] == x[(n - 1) as int - j],
    {
        if x[i] != x[n - 1 - i] {
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert forall|k: int| 0 <= k < n as int implies x[k] == x[(n - 1) as int - k] by {
            if k < (n / 2) as int {
                assert(x[k] == x[(n - 1) as int - k]);
            } else {
                let j = (n - 1) as int - k;
                assert(0 <= j < (n / 2) as int);
                assert(x[j] == x[(n - 1) as int - j]);
                assert((n - 1) as int - j == k);
            }
        }
    }
    
    true
}
// </vc-code>

}
fn main() {}