// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn genfromtxt(input: Vec<String>, delimiter: String, fill_value: f32, skip_header: usize) -> (result: Vec<Vec<f32>>)
    requires 
        skip_header < input.len(),
    ensures
        result.len() == input.len() - skip_header,
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let line_idx = (i + skip_header as int) as usize;
            line_idx < input.len()
        },
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): fixed compilation error by using exclusive range instead of inclusive */
    let mut result = Vec::new();
    for val in skip_header..input.len()
        invariant
            result.len() as int == (val as int - skip_header as int)
    {
        let mut inner_vec = Vec::new();
        result.push(inner_vec);
    }
    result
}
// </vc-code>

}
fn main() {}