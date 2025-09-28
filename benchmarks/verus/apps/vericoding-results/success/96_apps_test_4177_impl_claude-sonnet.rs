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
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == 'x',
        decreases s.len() - i
    {
        result.push('x');
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}