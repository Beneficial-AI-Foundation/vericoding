use vstd::prelude::*;

fn main() {}

verus! {

fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 2): fixed type consistency between usize and int */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] arr[j][0],
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 2): cast i to int for length assertion */
        assert(0 <= i < arr.len());
        assert(arr[i as int].len() > 0);
        
        result.push(arr[i][0]);
        i += 1;
    }
    
    result
}

} // verus!