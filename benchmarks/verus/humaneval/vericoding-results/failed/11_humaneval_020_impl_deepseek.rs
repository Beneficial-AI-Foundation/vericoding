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
proof fn lemma_abs_diff_properties(x: int, y: int) 
    ensures 
        abs_diff(x, y) >= 0,
        abs_diff(x, y) == abs_diff(y, x)
{
}

proof fn lemma_valid_input_implies_nonempty(numbers: Seq<int>)
    requires
        valid_input(numbers)
    ensures
        numbers.len() >= 2
{
}

proof fn lemma_contains_implies_exist(numbers: Seq<int>, pair: (int, int))
    requires
        is_optimal_pair(numbers, pair)
    ensures
        numbers.contains(pair.0) && numbers.contains(pair.1) && pair.0 <= pair.1
{
}

fn find_min_diff_pair(numbers: &Vec<i8>) -> (usize, usize)
    requires
        numbers@.len() >= 2
    ensures
        0 <= result.0 < numbers@.len(),
        0 <= result.1 < numbers@.len(),
        result.0 != result.1,
        forall|i: int, j: int| 0 <= i < numbers@.len() && 0 <= j < numbers@.len() && i != j ==> 
            abs_diff(numbers[i] as int, numbers[j] as int) >= abs_diff(numbers[result.0] as int, numbers[result.1] as int)
{
    let mut min_i: usize = 0;
    let mut min_j: usize = 1;
    ghost {
        let ghost_min_diff = abs_diff(numbers[min_i] as int, numbers[min_j] as int);
    }
    
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers@.len(),
            0 <= min_i < numbers@.len(),
            0 <= min_j < numbers@.len(),
            min_i != min_j,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < i && k != l ==> 
                abs_diff(numbers[k] as int, numbers[l] as int) >= abs_diff(numbers[min_i] as int, numbers[min_j] as int),
            forall|m: int, n: int| 0 <= m < numbers@.len() && 0 <= n < numbers@.len() && m != n ==>
                abs_diff(numbers[m] as int, numbers[n] as int) >= abs_diff(numbers[min_i] as int, numbers[min_j] as int)
        decreases numbers@.len() - i
    {
        let mut j: usize = i + 1;
        while j < numbers.len()
            invariant
                i + 1 <= j <= numbers@.len(),
                forall|k: int| i <= k < j && k != i ==> 
                    abs_diff(numbers[i] as int, numbers[k] as int) >= abs_diff(numbers[min_i] as int, numbers[min_j] as int)
            decreases numbers@.len() - j
        {
            let current_diff = abs_diff(numbers[i] as int, numbers[j] as int);
            if current_diff < abs_diff(numbers[min_i] as int, numbers[min_j] as int) {
                min_i = i;
                min_j = j;
            }
            j += 1;
        }
        i += 1;
    }
    (min_i, min_j)
}
// </vc-helpers>

// <vc-spec>
fn find_closest_elements(numbers: Vec<i8>) -> (result: (i8, i8))
    requires valid_input(numbers@.map(|_index, x| x as int))
    ensures is_optimal_pair(numbers@.map(|_index, x| x as int), (result.0 as int, result.1 as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix ghost variable declaration */
    proof {
        lemma_valid_input_implies_nonempty(numbers@.map(|_index, x| x as int));
    }
    
    let indices = find_min_diff_pair(&numbers);
    let a = numbers[indices.0];
    let b = numbers[indices.1];
    
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}
// </vc-code>


}

fn main() {}