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
/* helper modified by LLM (iteration 4): added bounds checking lemmas */
proof fn lemma_valid_input_bounds(lines: Seq<Seq<char>>)
    requires valid_input(lines)
    ensures
        lines.len() == 3,
        0 < lines.len(),
        1 < lines.len(),
        2 < lines.len(),
        lines[0].len() == 3,
        lines[1].len() == 3,
        lines[2].len() == 3,
        0 < lines[0].len(),
        1 < lines[0].len(),
        0 < lines[1].len(),
        1 < lines[1].len(),
        0 < lines[2].len(),
        2 < lines[2].len(),
{
}

proof fn lemma_vec_bounds(lines: Vec<Vec<char>>)
    requires valid_input(lines@.map(|i: int, v: Vec<char>| v@))
    ensures
        lines.len() == 3,
        0 < lines.len() as int,
        1 < lines.len() as int,
        2 < lines.len() as int,
        lines[0].len() == 3,
        lines[1].len() == 3,
        lines[2].len() == 3,
        0 < lines[0].len() as int,
        1 < lines[0].len() as int,
        0 < lines[1].len() as int,
        1 < lines[1].len() as int,
        0 < lines[2].len() as int,
        2 < lines[2].len() as int,
{
    let mapped = lines@.map(|i: int, v: Vec<char>| v@);
    lemma_valid_input_bounds(mapped);
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
    /* code modified by LLM (iteration 4): added bounds checking proof */
    proof {
        lemma_vec_bounds(lines);
    }
    
    let mut result = Vec::new();
    
    result.push(lines[0][0]);
    result.push(lines[1][1]);
    result.push(lines[2][2]);
    result.push('\n');
    
    proof {
        let mapped_lines = lines@.map(|i: int, v: Vec<char>| v@);
        let diagonal = extract_diagonal(mapped_lines);
        
        lemma_valid_input_bounds(mapped_lines);
        
        assert(diagonal.len() == 3);
        assert(diagonal[0] == lines@[0]@[0]);
        assert(diagonal[1] == lines@[1]@[1]);
        assert(diagonal[2] == lines@[2]@[2]);
        
        assert(result@.len() == 4);
        assert(result@[0] == lines@[0]@[0]);
        assert(result@[1] == lines@[1]@[1]);
        assert(result@[2] == lines@[2]@[2]);
        assert(result@[3] == '\n');
        
        assert(result@ == diagonal.push('\n'));
    }
    
    result
}
// </vc-code>


}

fn main() {}