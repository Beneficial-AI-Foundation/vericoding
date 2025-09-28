use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: int, b: int) -> int {
    if a - b < 0 { b - a } else { a - b }
}

proof fn abs_diff_symmetric(a: int, b: int)
    ensures abs_diff(a, b) == abs_diff(b, a)
{
}

proof fn abs_diff_non_negative(a: int, b: int)
    ensures abs_diff(a, b) >= 0
{
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
    let mut i: usize = 0;
    while i < numbers.len() as usize
        invariant
            0 <= i <= numbers.len(),
            forall|x: int, y: int| 0 <= x < i && 0 <= y < x ==> abs_diff(numbers[x], numbers[y]) >= threshold,
    {
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i < numbers.len(),
                forall|x: int, y: int| 0 <= x < i && 0 <= y < x ==> abs_diff(numbers[x], numbers[y]) >= threshold,
                forall|y: int| 0 <= y < j ==> abs_diff(numbers[i as int], numbers[y]) >= threshold,
        {
            if abs_diff(numbers[i as int], numbers[j as int]) < threshold {
                assert(0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j);
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {
}

}