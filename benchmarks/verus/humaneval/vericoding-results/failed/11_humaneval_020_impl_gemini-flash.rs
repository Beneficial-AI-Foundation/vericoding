// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(x: int, y: int) -> int {
        if x >= y { x - y } else { y - x }
    }
    
spec fn valid_input(numbers: Seq<int>) -> bool {
        numbers.len() >= 2
    }
    
spec fn is_optimal_pair(numbers: Seq<int>, pair: (int, int)) -> bool {
        numbers.contains(pair.0) &&
        numbers.contains(pair.1) &&
        pair.0 <= pair.1 &&
        forall|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j ==>
            abs_diff(numbers[i], numbers[j]) >= abs_diff(pair.0, pair.1)
    }
    
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [No changes needed in `lemma_abs_diff_min_implies_optimal` helper, as the previous iteration fixed any issues. This is a placeholder to fulfill the requirement of modifying helpers if needed.] */
proof fn lemma_abs_diff_min_implies_optimal(numbers_vec: &Vec<i8>, numbers_seq: Seq<int>, min_diff: int, val1: int, val2: int)
    requires
        valid_input(numbers_seq),
        min_diff >= 0,
        numbers_seq.contains(val1),
        numbers_seq.contains(val2),
        val1 <= val2,
        abs_diff(val1, val2) == min_diff,
        forall|i: int, j: int| 0 <= i < numbers_seq.len() && 0 <= j < numbers_seq.len() && i != j ==> abs_diff(numbers_seq[i], numbers_seq[j]) >= min_diff
    ensures
        is_optimal_pair(numbers_seq, (val1, val2))
{
    // All required conditions for `is_optimal_pair` are already present in the `requires` clause.
    // No further proof steps are needed, as Verus can directly check if the conditions imply the `ensures` clause.
}
// </vc-helpers>

// <vc-spec>
fn find_closest_elements(numbers: Vec<i8>) -> (result: (i8, i8))
    requires valid_input(numbers@.map(|_index, x| x as int))
    ensures is_optimal_pair(numbers@.map(|_index, x| x as int), (result.0 as int, result.1 as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Changed `as nat` and `as int` casts to `as usize` for indexing, and handled conversions between `i8` and `int` for calculations and comparisons more explicitly to resolve compilation errors related to `nat`/`int` in non-ghost code.] */
{
    let numbers_seq = numbers@.map(|_index, x: i8| x as int);

    let mut min_diff: int = abs_diff(numbers_seq.index(0), numbers_seq.index(1));
    let mut result_pair: (i8, i8);

    if numbers_seq.index(0) <= numbers_seq.index(1) {
        result_pair = (numbers.index(0), numbers.index(1));
    } else {
        result_pair = (numbers.index(1), numbers.index(0));
    }

    let mut i: usize = 0;
    while i < numbers_seq.len()
        invariant
            0 <= i as int <= numbers_seq.len() as int,
            min_diff >= 0,
            numbers_seq.contains(result_pair.0 as int),
            numbers_seq.contains(result_pair.1 as int),
            result_pair.0 as int <= result_pair.1 as int,
            abs_diff(result_pair.0 as int, result_pair.1 as int) == min_diff,

            forall|idx1: int, idx2: int| {
                #![trigger abs_diff(numbers_seq[idx1], numbers_seq[idx2])]
                0 <= idx1 < numbers_seq.len() && 0 <= idx2 < numbers_seq.len() && idx1 < idx2
                && (idx1 < i as int || (idx1 == i as int && idx2 < (numbers_seq.len() as int)))
                ==> abs_diff(numbers_seq[idx1], numbers_seq[idx2]) >= min_diff
            }
        decreases numbers_seq.len() - i
    {
        let mut j: usize = i + 1;
        while j < numbers_seq.len()
            invariant
                i as int < j as int <= numbers_seq.len() as int,
                min_diff >= 0,
                numbers_seq.contains(result_pair.0 as int),
                numbers_seq.contains(result_pair.1 as int),
                result_pair.0 as int <= result_pair.1 as int,
                abs_diff(result_pair.0 as int, result_pair.1 as int) == min_diff,
                
                forall|idx1: int, idx2: int| {
                    #![trigger abs_diff(numbers_seq[idx1], numbers_seq[idx2])]
                    0 <= idx1 < numbers_seq.len() && 0 <= idx2 < numbers_seq.len() && idx1 < idx2
                    && (idx1 < i as int || (idx1 == i as int && idx2 < j as int))
                    ==> abs_diff(numbers_seq[idx1], numbers_seq[idx2]) >= min_diff
                }
            decreases numbers_seq.len() - j
        {
            let diff = abs_diff(numbers_seq.index(j), numbers_seq.index(i));
            
            if diff < min_diff {
                min_diff = diff;
                if numbers_seq.index(i) <= numbers_seq.index(j) {
                    result_pair = (numbers.index(i), numbers.index(j));
                } else {
                    result_pair = (numbers.index(j), numbers.index(i));
                }
            }
            j = j + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_abs_diff_min_implies_optimal(&numbers, numbers_seq, min_diff, result_pair.0 as int, result_pair.1 as int);
    }
    result_pair
}
// </vc-code>


}

fn main() {}