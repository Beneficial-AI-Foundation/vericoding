// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(lines: Seq<Seq<char>>) -> bool {
    lines.len() == 3 && forall|i: int| 0 <= i < 3 ==> lines[i].len() == 3
}

spec fn extract_diagonal(lines: Seq<Seq<char>>) -> Seq<char>
    recommends valid_input(lines)
{
    seq![lines[0][0], lines[1][1], lines[2][2]]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma to extract lengths from valid_input */
proof fn lemma_valid_input_implies_lengths(s: Seq<Seq<char>>)
    requires valid_input(s)
    ensures 
        s[0].len() == 3,
        s[1].len() == 3,
        s[2].len() == 3
{
    reveal(valid_input);
    assert(s[0].len() == 3);
    assert(s[1].len() == 3);
    assert(s[2].len() == 3);
}
// </vc-helpers>

// <vc-spec>
fn solve(lines: Vec<Vec<char>>) -> (result: Vec<char>)
    requires valid_input(lines@.map(|i: int, v: Vec<char>| v@))
    ensures 
        result@.len() == 4 &&
        result@[0] == lines@[0]@[0] &&
        result@[1] == lines@[1]@[1] &&
        result@[2] == lines@[2]@[2] &&
        result@[3] == '\n' &&
        result@ == extract_diagonal(lines@.map(|i: int, v: Vec<char>| v@)).push('\n')
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added helper lemma and used it to prove vector lengths */
    proof {
        let s = lines@.map(|i: int, v: Vec<char>| v@);
        lemma_valid_input_implies_lengths(s);
    }
    let mut result = Vec::new();
    result.push(lines[0][0]);
    result.push(lines[1][1]);
    result.push(lines[2][2]);
    result.push('\n');
    result
}
// </vc-code>


}

fn main() {}