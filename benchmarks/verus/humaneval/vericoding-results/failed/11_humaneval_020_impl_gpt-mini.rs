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
{
proof fn abs_diff_nonneg(x: int, y: int)
    ensures
        abs_diff(x, y) >= 0,
{
    if x >= y {
        assert x - y >= 0;
    } else {
        assert y - x >= 0;
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
    let n = numbers.len() as int;
    // initialize with first two elements (precondition guarantees at least 2)
    let mut min_idx_a: int = 0;
    let mut min_idx_b: int = 1;
    let mut min_a: i8 = numbers.get(min_idx_a as usize);
    let mut min_b: i8 = numbers.get(min_idx_b as usize);
    let mut min_diff: int = if min_a as int >= min_b as int { min_a as int - min_b as int } else { min_b as int - min_a as int };

    let mut i: int = 1;
    while i < n
        invariant
            1 <= i,
            i <= n,
            forall|p: int, q: int| 0 <= p < q < i ==> abs_diff(numbers@[p] as int, numbers@[q] as int) >= min_diff,
        decreases n - i
    {
        let mut j: int = 0;
        while j < i
            invariant
                0 <= j,
                j <= i,
                forall|p: int, q: int| 0 <= p < q < i ==> abs_diff(numbers@[p] as int, numbers@[q] as int) >= min_diff,
                forall|p: int| 0 <= p < j ==> abs_diff(numbers@[p] as int, numbers@[i] as int) >= min_diff,
            decreases i - j
        {
            let a = numbers.get(j as usize);
            let b = numbers.get(i as usize);
            let diff: int = if a as int >= b as int { a as int - b as int } else { b as int - a as int };
            if diff < min_diff {
                if a <= b {
                    min_a = a;
                    min_b = b;
                    min_idx_a = j;
                    min_idx_b = i;
                } else {
                    min_a = b;
                    min_b = a;
                    min_idx_a = i;
                    min_idx_b = j;
                }
                min_diff = diff;
            }
            j += 1;
        }
        i += 1;
    }

    proof {
        // elements at stored indices correspond to returned values
        assert min_a as int == numbers@[min_idx_a] as int;
        assert min_b as int == numbers@[min_idx_b] as int;
        // they are contained in the sequence
        assert numbers@.contains(min_a as int);
        assert numbers@.contains(min_b as int);
        // ordering ensured on updates
        assert min_a <= min_b;
        // the outer loop invariant at exit ensures optimality relative to min_diff
        assert forall|p: int, q: int| 0 <= p < q < n ==> abs_diff(numbers@[p] as int, numbers@[q] as int) >= min_diff;
        // min_diff corresponds to the difference of the returned pair
        assert abs_diff(numbers@[min_idx_a] as int, numbers@[min_idx_b] as int) == min_diff;
    }

    (min_a, min_b)
}

// </vc-code>


}

fn main() {}