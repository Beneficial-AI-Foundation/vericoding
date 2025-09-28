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

spec fn map_preserves_len<T, U>(s: Seq<T>, f: spec_fn(int, T) -> U) -> bool {
    s.map(f).len() == s.len()
}
/* helper modified by LLM (iteration 4): Fixed deprecated FnSpec -> spec_fn */
proof fn vec_index_valid_proof(lines: Seq<Seq<char>>, i: int, j: int)
    requires
        valid_input(lines),
        0 <= i < 3,
        0 <= j < 3,
    ensures
        0 <= i < lines.len(),
        0 <= j < lines[i].len(),
{
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
    /* code modified by LLM (iteration 4): Added bounds checking and proof for safe indexing */
    proof {
        vec_index_valid_proof(lines@.map(|k: int, v: Vec<char>| v@), 0, 0);
        vec_index_valid_proof(lines@.map(|k: int, v: Vec<char>| v@), 1, 1);
        vec_index_valid_proof(lines@.map(|k: int, v: Vec<char>| v@), 2, 2);
    }
    let a = lines[0][0];
    let b = lines[1][1];
    let c = lines[2][2];
    let mut result = Vec::new();
    result.push(a);
    result.push(b);
    result.push(c);
    result.push('\n');
    proof {
        assert(result@.len() == 4);
        assert(result@[0] == lines@[0]@[0]);
        assert(result@[1] == lines@[1]@[1]);
        assert(result@[2] == lines@[2]@[2]);
        assert(result@[3] == '\n');
    }
    result
}
// </vc-code>


}

fn main() {}