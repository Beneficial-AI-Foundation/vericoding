use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: int, b: int) -> int {
    if a - b < 0 { (b - a) } else { (a - b) }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (res: bool)
    requires threshold >= 0,
    ensures ({
        &&& (res ==> exists|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j && 
            abs_diff(numbers[i], numbers[j]) < threshold)
        &&& (!res ==> forall|i: int, j: int| 1 <= i < numbers.len() && 0 <= j < i ==> 
            abs_diff(numbers[i], numbers[j]) >= threshold)
    }),
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();

    if n < 2 {
        // If there are fewer than 2 elements, no pair can be found.
        assert(! (exists|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j && 
            abs_diff(numbers.view_at(i), numbers.view_at(j)) < threshold));
        false // Should be false as no pair can be found
    } else {
        let mut i: nat = 0;
        let mut result: bool = false;

        while i < n && !result
            invariant
                0 <= i <= n,
                result ==> (exists|idx_a: int, idx_b: int| 0 <= idx_b < idx_a < i as int && abs_diff(numbers.view_at(idx_a), numbers.view_at(idx_b)) < threshold),
                !result ==> (forall|idx_a: int, idx_b: int| 0 <= idx_b < idx_a < i as int ==> abs_diff(numbers.view_at(idx_a), numbers.view_at(idx_b)) >= threshold),
        {
            let mut j: nat = 0;
            while j < i && !result
                invariant
                    0 <= j <= i,
                    result ==> (exists|idx_a: int, idx_b: int| (0 <= idx_b < idx_a < i as int && abs_diff(numbers.view_at(idx_a), numbers.view_at(idx_b)) < threshold)
                                || (idx_a == i as int && 0 <= idx_b < j as int && abs_diff(numbers.view_at(idx_a), numbers.view_at(idx_b)) < threshold)),
                    !result ==> (forall|idx_b_inner: int| 0 <= idx_b_inner < j as int ==> abs_diff(numbers.view_at(i as int), numbers.view_at(idx_b_inner)) >= threshold),
                    !result ==> (forall|idx_a: int, idx_b: int| 0 <= idx_b < idx_a < i as int ==> abs_diff(numbers.view_at(idx_a), numbers.view_at(idx_b)) >= threshold),
            {
                proof {
                    assert(i as int >= 0);
                    assert(j as int >= 0);
                }
                if abs_diff(numbers.view_at(i as int), numbers.view_at(j as int)) < threshold {
                    result = true;
                }
                j = j + 1;
            }
            i = i + 1;
        }

        if result {
            assert(exists|i_res: int, j_res: int| 0 <= j_res < i_res < numbers.len() &&
                abs_diff(numbers.view_at(i_res), numbers.view_at(j_res)) < threshold);
        } else {
            assert(forall|i_res: int, j_res: int| 0 <= j_res < i_res < numbers.len() ==>
                abs_diff(numbers.view_at(i_res), numbers.view_at(j_res)) >= threshold);
        }
        result
    }
}
// </vc-code>

fn main() {
}

}