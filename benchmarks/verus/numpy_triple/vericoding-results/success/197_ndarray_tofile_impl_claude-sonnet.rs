// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added file writing helper function */
fn write_to_file(filename: String, data: Vec<f32>) -> bool {
    // Placeholder for actual file I/O
    true
}
// </vc-helpers>

// <vc-spec>
fn numpy_tofile(arr: Vec<f32>, filename: String) -> (result: ())
    requires true,
    ensures result == ()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    // Write array data to file
    let mut file_data = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            file_data.len() == i,
        decreases arr.len() - i
    {
        file_data.push(arr[i]);
        i += 1;
    }
    
    // Simulate file writing operation
    let _written = write_to_file(filename, file_data);
    
    ()
}
// </vc-code>

}
fn main() {}