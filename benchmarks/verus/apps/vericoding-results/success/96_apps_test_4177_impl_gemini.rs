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
fn create_x_vec(len: usize) -> (result: Vec<char>)
    requires
        len <= 100,
    ensures
        result.len() == len,
        forall|i: int| 0 <= i < len ==> result@[i] == 'x',
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == 'x',
        decreases len - i
    {
        result.push('x');
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    let result = create_x_vec(s.len());
    result
}
// </vc-code>


}

fn main() {}