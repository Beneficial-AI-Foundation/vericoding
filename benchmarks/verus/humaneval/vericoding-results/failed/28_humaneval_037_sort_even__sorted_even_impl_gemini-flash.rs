// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding an invariant to the `while` loop to specify that odd-indexed elements remain unchanged and even-indexed elements are sorted. */

// </vc-helpers>

// <vc-spec>
fn sorted_even(a: Vec<i8>) -> (sorted: Vec<i8>)
    requires 
        a@.len() > 0
    ensures 
        sorted@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j && 2 * i < sorted@.len() && 2 * j < sorted@.len() ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * j],
        forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] sorted@[i] == #[trigger] a@[i],
        a@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type mismatches between `int` and native integer types by consistently using `int` for loop counters and indices when performing arithmetic, and explicitly casting to `usize`/`nat` only when necessary for array access. Also, explicitly unwrapped Option values when accessing array elements */
{
    let mut result = a;

    let mut i: int = 0;
    while i < result@.len()
        invariant
            0 <= i <= result@.len(),
            result@.len() == a@.len(),
            forall|k: int| 0 <= k < result@.len() && k % 2 == 1 ==> result@[k] == a@[k],
            forall|x: int, y: int|
                0 <= x < y && (2 * x) < i && (2 * y) < i
                ==>
                result@[(2 * x) as nat] <= result@[(2 * y) as nat],
            a@.to_multiset() == result@.to_multiset()
        decreases result@.len() - i
    {
        // Find the smallest even element in the unsorted part
        let mut min_even_val: i8 = i8::MAX; // Max i8
        let mut min_even_idx: int = -1;

        let current_i = i;
        let mut j: int = current_i / 2;

        while (2 * j) < result@.len()
            invariant
                (current_i / 2) <= j,
                (2 * j) <= result@.len(),
                result@.len() == a@.len(),
                forall|k: int| 0 <= k < result@.len() && k % 2 == 1 ==> result@[k] == a@[k],
                forall|x: int, y: int|
                    0 <= x < y && (2 * x) < current_i && (2 * y) < current_i
                    ==>
                    result@[(2 * x) as nat] <= result@[(2 * y) as nat],
                a@.to_multiset() == result@.to_multiset(),
                (min_even_idx != -1) ==> (0 <= min_even_idx < result@.len() && min_even_idx % 2 == 0),
                forall|k: int|
                    ((current_i / 2) <= k && k < j && (2 * k) < result@.len())
                    ==>
                    result@[(2 * k) as nat] >= min_even_val
            decreases result@.len() - (2 * j)
        {
            if (2 * j) < result@.len() && result.get((2 * j) as usize).unwrap() < min_even_val {
                min_even_val = result.get((2 * j) as usize).unwrap();
                min_even_idx = 2 * j;
            }
            j = j + 1;
        }

        let current_even_pos = 2 * (i / 2);
        if current_even_pos < result@.len() {
            if min_even_idx != -1 {
                let temp = result.get(current_even_pos as usize).unwrap();
                result.set(current_even_pos as usize, result.get(min_even_idx as usize).unwrap());
                result.set(min_even_idx as usize, temp);
            }
        }

        i = i + 2; // Increment `i` by 2 to process next even position
    }

    result
}
// </vc-code>


}

fn main() {}