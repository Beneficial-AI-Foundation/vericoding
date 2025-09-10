use vstd::prelude::*;

verus! {

fn genfromtxt(input: Vec<String>, delimiter: String, fill_value: f32, skip_header: usize) -> (result: Vec<Vec<f32>>)
    requires 
        skip_header < input.len(),
    ensures
        result.len() == input.len() - skip_header,
        forall|i: int| 0 <= i < result.len() ==> {
            let line_idx = (i + skip_header as int) as usize;
            line_idx < input.len()
        },
{
    assume(false);
    unreached()
}

}
fn main() {}