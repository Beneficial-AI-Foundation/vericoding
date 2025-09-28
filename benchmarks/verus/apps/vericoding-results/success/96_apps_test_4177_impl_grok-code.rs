// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] && s[i] <= 'z'
}

spec fn valid_output(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() == s.len() && forall|i: int| 0 <= i < result.len() ==> result[i] == 'x'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let sz = s.len();

    for i in 0..sz
        invariant
            result.len() == i,
            sz <= 100,
            forall|k: int| 0 <= k < i ==> (#[trigger] result@[k]) == 'x',
    {
        result.push('x');
    }
    
    result
}
// </vc-code>


}

fn main() {}