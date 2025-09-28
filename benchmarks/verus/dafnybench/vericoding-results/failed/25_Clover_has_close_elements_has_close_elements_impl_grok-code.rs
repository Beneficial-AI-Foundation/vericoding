use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: int, b: int) -> int {
    if a - b < 0 { b - a } else { a - b }
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
    let mut found: bool = false;
    let mut i: usize = 0;
    while i < numbers.len() as usize
        invariant
            0 <= (i as int) <= numbers.len(),
            (forall |k: int, l: int| #[trigger] abs_diff(numbers[k], numbers[l]) >= threshold ==> (0 <= k < (i as int) && 0 <= l < numbers.len() && k != l))
    {
        let mut j: usize = 0;
        while j < numbers.len() as usize
            invariant
                0 <= (j as int) <= numbers.len(),
                (forall |l: int| #[trigger] abs_diff(numbers[i as int], numbers[l]) >= threshold ==> (0 <= l < (j as int) && (i as int) != l))
        {
            if ghost((i as int) != (j as int) && abs_diff(numbers[i as int], numbers[j as int]) < threshold) {
                found = true;
                assert(ghost(0 <= (i as int) < numbers.len() && 0 <= (j as int) < numbers.len() && (i as int) != (j as int) && abs_diff(numbers[i as int], numbers[j as int]) < threshold));
            }
            j += 1;
        }
        assert(forall |l: int| 0 <= l < numbers.len() && l != (i as int) ==> abs_diff(numbers[i as int], numbers[l]) >= threshold);
        i += 1;
    }
    found
}
// </vc-code>

fn main() {
}

}