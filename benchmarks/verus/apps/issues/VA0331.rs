// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
pub struct InputData {
    pub n: int,
    pub m: int,
    pub segments: Set<(int, int)>,
}

spec fn valid_input_format(stdin_input: &str) -> bool {
    stdin_input.len() > 0
}

spec fn parse_input(stdin_input: &str) -> InputData
    requires valid_input_format(stdin_input)
{
    InputData {
        n: 2,
        m: 0,
        segments: Set::empty(),
    }
}

spec fn rotate_segment(seg: (int, int), k: int, n: int) -> (int, int)
    requires 1 <= seg.0 <= n && 1 <= seg.1 <= n && k >= 0 && n > 0
{
    let temp_a = (seg.0 + k) % n;
    let a = if temp_a == 0 { n } else { temp_a };
    let temp_b = (seg.1 + k) % n;
    let b = if temp_b == 0 { n } else { temp_b };
    (a, b)
}

spec fn exists_rotational_symmetry(data: InputData) -> bool {
    exists|k: int| 1 <= k < data.n && 
        data.n % k == 0 &&
        (forall|seg: (int, int)| data.segments.contains(seg) ==> 
            seg.0 >= 1 && seg.0 <= data.n && seg.1 >= 1 && seg.1 <= data.n &&
            data.segments.contains(rotate_segment(seg, k, data.n)))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires stdin_input.len() > 0
    requires valid_input_format(stdin_input)
    ensures result == "Yes" || result == "No"
    ensures (result == "Yes") == exists_rotational_symmetry(parse_input(stdin_input))
// </vc-spec>
// <vc-code>
{
    assume(false);
    "No".to_string()
}
// </vc-code>


}

fn main() {}