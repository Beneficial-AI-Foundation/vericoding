use vstd::prelude::*;

verus! {

fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): added bounds checks and strengthened invariants for verification */
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] arr[j][0],
        decreases arr.len() - i
    {
        /* code modified by LLM (iteration 3): fixed operator precedence by adding parentheses around the comparison */
        assert(0 <= (i as int) && (i as int) < arr.len());
        assert(arr[i as int].len() > 0);
        result.push(arr[i][0]);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}