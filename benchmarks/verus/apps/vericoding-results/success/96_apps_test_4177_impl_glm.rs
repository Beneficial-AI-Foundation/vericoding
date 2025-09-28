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
/* helper modified by LLM (iteration 3): fixed type conversion to nat for Seq::new */
fn create_x_vector(len: usize) -> (v: Vec<char>)
    ensures v@ == Seq::new(len as nat, |i: int| 'x')
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    let n = len;
    while i < n
        invariant
            i <= n,
            v@ == Seq::new(i as nat, |j: int| 'x'),
        decreases (n - i) as int
    {
        v.push('x');
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no changes needed, using fixed helper function */
{
    let result = create_x_vector(s.len());
    result
}
// </vc-code>


}

fn main() {}