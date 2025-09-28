// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(arr: Seq<int>) -> bool {
    true
}

spec fn distinct_non_zero_count(arr: Seq<int>) -> int {
    Set::<int>::new(|x: int| arr.contains(x) && x != 0).len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper `vec_to_seq_int` does not require any modification. The error was in the main code. */
spec fn vec_to_seq_int(arr: Vec<i8>) -> Seq<int> {
    arr@.map(|i, x| x as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Vec<i8>) -> (result: i8)
    requires 
        valid_input(vec_to_seq_int(arr))
    ensures 
        result >= 0,
        result as int <= arr@.len(),
        result as int == distinct_non_zero_count(vec_to_seq_int(arr))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed `current_val_i as int` to `current_val_i_ghost` within the `seen_non_zeros.insert` call to ensure the argument is a ghost `int` type, resolving the compilation error. */
{
    let mut seen_non_zeros: Set<int> = Set::empty();
    let mut i: int = 0;

    while i < arr.len()
        invariant 
            0 <= i <= arr.len(),
            forall|idx: int| 0 <= idx < i ==> {
                let current_val_at_idx: i8 = arr@[idx];
                (current_val_at_idx as int != 0) ==> seen_non_zeros.contains(current_val_at_idx as int)
            },
            forall|x: int| seen_non_zeros.contains(x) ==> ( // All elements in seen_non_zeros must come from arr[0..i-1] and not be 0
                exists|idx: int| 0 <= idx < i && arr@[idx] as int == x && x != 0
            ),
            seen_non_zeros.len() == distinct_non_zero_count(vec_to_seq_int(arr).subsequence(0, i))
        decreases arr.len() - i
    {
        let current_val_i: i8 = arr@[i];
        let current_val_i_ghost = current_val_i as int; // Introduce a ghost variable for the int conversion
        if current_val_i != 0 {
            seen_non_zeros = seen_non_zeros.insert(current_val_i_ghost);
        }
        i = i + 1;
    }

    (seen_non_zeros.len() as i8)
}
// </vc-code>


}

fn main() {}