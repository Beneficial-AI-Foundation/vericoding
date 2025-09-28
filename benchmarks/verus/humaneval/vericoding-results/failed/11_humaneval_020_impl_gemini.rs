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
/* helper modified by LLM (iteration 2): added a symmetry lemma to aid verification */
lemma fn lemma_abs_diff_symmetric(x: int, y: int)
    ensures abs_diff(x, y) == abs_diff(y, x)
{
}

fn compute_abs_diff(a: i8, b: i8) -> (res: i32)
    ensures res as int == abs_diff(a as int, b as int),
{
    let a_int = a as i32;
    let b_int = b as i32;
    if a_int >= b_int {
        a_int - b_int
    } else {
        b_int - a_int
    }
}
// </vc-helpers>

// <vc-spec>
fn find_closest_elements(numbers: Vec<i8>) -> (result: (i8, i8))
    requires valid_input(numbers@.map(|_index, x| x as int))
    ensures is_optimal_pair(numbers@.map(|_index, x| x as int), (result.0 as int, result.1 as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by using 'ghost let' and removing redundant invariants */
    ghost let s = numbers@.map(|_index, x| x as int);
    
    // Initialize with the first two elements, which is valid due to the `requires` clause.
    let n0 = numbers[0];
    let n1 = numbers[1];

    let mut result_pair = if n0 <= n1 { (n0, n1) } else { (n1, n0) };
    let mut min_diff = compute_abs_diff(n0, n1);

    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            s.contains(result_pair.0 as int),
            s.contains(result_pair.1 as int),
            result_pair.0 <= result_pair.1,
            min_diff as int == abs_diff(result_pair.0 as int, result_pair.1 as int),
            forall|a: int, b: int| 
                0 <= a < i && a < b < numbers.len() ==> 
                abs_diff(s[a], s[b]) >= min_diff as int,
        decreases numbers.len() - i
    {
        let mut j: usize = i + 1;
        while j < numbers.len()
            invariant
                0 <= i < numbers.len(),
                s.contains(result_pair.0 as int),
                s.contains(result_pair.1 as int),
                result_pair.0 <= result_pair.1,
                min_diff as int == abs_diff(result_pair.0 as int, result_pair.1 as int),
                i < j <= numbers.len(),
                forall|a: int, b: int|
                    (0 <= a < i && a < b < numbers.len()) || (a == i && i < b < j) ==> 
                    abs_diff(s[a], s[b]) >= min_diff as int,
            decreases numbers.len() - j
        {
            let p_i = numbers[i];
            let p_j = numbers[j];
            let current_diff = compute_abs_diff(p_i, p_j);

            if current_diff < min_diff {
                min_diff = current_diff;
                if p_i <= p_j {
                    result_pair = (p_i, p_j);
                } else {
                    result_pair = (p_j, p_i);
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    result_pair
}
// </vc-code>


}

fn main() {}