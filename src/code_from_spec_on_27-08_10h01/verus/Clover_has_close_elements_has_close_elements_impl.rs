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

proof fn abs_diff_nonneg(a: int, b: int)
    ensures abs_diff(a, b) >= 0
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    while i < numbers.len()
        invariant 
            0 <= i <= numbers.len(),
            forall|x: int, y: int| 0 <= x < i && 0 <= y < x ==> abs_diff(numbers[x], numbers[y]) >= threshold,
    {
        let mut j: usize = 0;
        while j < i
            invariant 
                0 <= j <= i < numbers.len(),
                forall|x: int, y: int| 0 <= x < i && 0 <= y < x ==> abs_diff(numbers[x], numbers[y]) >= threshold,
                forall|k: int| 0 <= k < j ==> abs_diff(numbers[i as int], numbers[k]) >= threshold,
        {
            let ghost i_int = i as int;
            let ghost j_int = j as int;
            if abs_diff(numbers[i_int], numbers[j_int]) < threshold {
                proof {
                    assert(0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j);
                    assert(abs_diff(numbers[i_int], numbers[j_int]) < threshold);
                }
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        assert(forall|x: int, y: int| 0 <= x < numbers.len() && 0 <= y < x ==> abs_diff(numbers[x], numbers[y]) >= threshold);
        assert(forall|x: int, y: int| 0 <= x < numbers.len() && 0 <= y < numbers.len() && x != y ==> {
            let (i, j) = if x < y { (y, x) } else { (x, y) };
            0 <= i < numbers.len() && 0 <= j < i
        });
    }
    false
}
// </vc-code>

fn main() {
}

}