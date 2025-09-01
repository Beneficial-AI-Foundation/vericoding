use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>
spec fn abs_diff_spec(a: i32, b: i32) -> int
    recommends a - b < i32::MAX && -(a - b) < i32::MAX
{
    if a < b { (b - a) as int } else { (a - b) as int }
}

proof fn abs_diff_property(a: i32, b: i32)
    requires
        a - b < i32::MAX && -(a - b) < i32::MAX
    ensures
        abs_diff_spec(a, b) == abs_spec(a - b)
{
    if a < b {
        assert(a - b < 0);
        assert(abs_spec(a - b) == -(a - b));
        assert(abs_diff_spec(a, b) == (b - a) as int);
        assert(b - a == -(a - b));
    } else {
        assert(a - b >= 0);
        assert(abs_spec(a - b) == a - b);
        assert(abs_diff_spec(a, b) == (a - b) as int);
    }
}

spec fn in_bounds(i: int, len: int) -> bool {
    0 <= i && i < len
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
    // pre-conditions-start
    requires
        threshold > 0,
        forall|i: int, j: int| 0 <= i && i < numbers.len() && 0 <= j && j < numbers.len() ==> numbers[i] - numbers[j] < i32::MAX && -(numbers[i] - numbers[j]) < i32::MAX
    // pre-conditions-end
    // post-conditions-start
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();
    let mut flag = false;
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|ii: int, jj: int| in_bounds(ii, i as int) && in_bounds(jj, n as int) && ii != jj ==> 
                abs_diff_spec(numbers[ii as int], numbers[jj as int]) >= threshold,
            flag == exists|ii: int, jj: int| in_bounds(ii, i as int) && in_bounds(jj, n as int) && ii != jj && 
                abs_diff_spec(numbers[ii as int], numbers[jj as int]) < threshold
    {
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                forall|jj: int| in_bounds(jj, j as int) && jj != i as int ==> 
                    abs_diff_spec(numbers[i], numbers[jj]) >= threshold,
                flag == exists|ii: int, jj: int| 
                    (in_bounds(ii, i as int) && in_bounds(jj, n as int) && ii != jj && 
                     abs_diff_spec(numbers[ii], numbers[jj]) < threshold) ||
                    (in_bounds(jj, j as int) && jj != i as int && 
                     abs_diff_spec(numbers[i], numbers[jj]) < threshold)
        {
            if i != j {
                proof {
                    abs_diff_property(numbers[i], numbers[j]);
                }
                let diff = if numbers[i] < numbers[j] {
                    numbers[j] - numbers[i]
                } else {
                    numbers[i] - numbers[j]
                };
                if diff < threshold {
                    flag = true;
                }
            }
            j += 1;
        }
        i += 1;
    }
    flag
}
// </vc-code>

fn main() {}
}