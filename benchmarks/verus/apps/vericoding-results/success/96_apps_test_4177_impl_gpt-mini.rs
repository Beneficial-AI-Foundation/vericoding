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
/* helper modified by LLM (iteration 2): predicate that all chars are 'x' */
spec fn all_x(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == 'x'
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): build result vector with 'x' for each input char */
    let mut res = Vec::<char>::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            res.len() == i,
            all_x(res@),
        decreases s.len() - i
    {
        res.push('x');
        i = i + 1;
    }
    res
}
// </vc-code>


}

fn main() {}