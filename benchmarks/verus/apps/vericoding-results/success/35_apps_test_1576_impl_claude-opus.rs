// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(t: Seq<char>) -> bool {
    t.len() >= 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(t: Vec<char>) -> (result: Vec<char>)
    requires valid_input(t@)
    ensures result@.len() == t@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let n = t.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == t.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result@[j] == t@[j],
        decreases n - i
    {
        result.push(t[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}