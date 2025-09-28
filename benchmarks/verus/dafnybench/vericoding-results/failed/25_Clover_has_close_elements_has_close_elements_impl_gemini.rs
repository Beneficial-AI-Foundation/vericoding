// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: int, b: int) -> int {
    if a - b < 0 { b - a } else { a - b }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed signature to use i64 */
fn abs_diff_exec(a: i64, b: i64) -> (res: i64)
    ensures res >= 0, res as int == abs_diff(a as int, b as int),
{
    if a > b { a - b } else { b - a }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (res: bool)
    requires threshold >= 0,
    ensures 
        (res ==> exists|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j && 
            abs_diff(numbers[i], numbers[j]) < threshold),
        (!res ==> forall|i: int, j: int| 1 <= i < numbers.len() && 0 <= j < i ==> 
            abs_diff(numbers[i], numbers[j]) >= threshold),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by running the loops in a proof block */
    let ghost res = proof {
        let mut i: nat = 1;
        let mut found = false;
        while i < numbers.len()
            invariant
                1 <= i <= numbers.len(),
                threshold >= 0,
                found == exists|k: int, l: int| 1 <= k < i && 0 <= l < k && abs_diff(numbers@[k], numbers@[l]) < threshold,
            decreases numbers.len() - i
        {
            if !found {
                let mut j: nat = 0;
                while j < i
                    invariant
                        0 <= j <= i,
                        i < numbers.len(),
                        !found,
                        forall|k: int, l: int| 1 <= k < i && 0 <= l < k ==> abs_diff(numbers@[k], numbers@[l]) >= threshold,
                        forall|k: int| 0 <= k < j ==> abs_diff(numbers@[i as int], numbers@[k]) >= threshold,
                    decreases i - j
                {
                    if abs_diff(numbers@[i as int], numbers@[j as int]) < threshold {
                        found = true;
                        break;
                    }
                    j = j + 1;
                }
            }
            if found {
                break;
            }
            i = i + 1;
        }
        found
    };

    if res {
        assert(exists|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j && 
            abs_diff(numbers[i], numbers[j]) < threshold) by {
            assert(res);
        }
        return true;
    } else {
        assert(forall|i: int, j: int| 1 <= i < numbers.len() && 0 <= j < i ==> 
            abs_diff(numbers[i], numbers[j]) >= threshold) by {
            assert(!res);
        }
        return false;
    }
}

// </vc-code>

}
fn main() {}