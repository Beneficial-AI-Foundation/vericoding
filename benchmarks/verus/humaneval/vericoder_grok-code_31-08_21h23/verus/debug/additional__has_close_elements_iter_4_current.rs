use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>
// (No changes needed, duplicate removed for clarity)
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
    let mut flag: bool = false;
    proof { assert(!flag); };
    for i in 0..numbers.len() {
        invariant(flag == exists|ii: int, jj: int| 0 <= ii && ii < i && 0 <= jj && jj < numbers@.len() && ii != jj && abs_spec(numbers@[ii] - numbers@[jj]) < threshold);
        for j in (i + 1)..numbers.len() {
            let diff: i64 = (numbers[i] as i64) - (numbers[j] as i64);
            let abs_diff: i64 = if diff < 0 { -diff } else { diff };
            if abs_diff < (threshold as i64) {
                proof {
                    assert(abs_diff as int == abs_spec(numbers@[i] - numbers@[j]));
                    assert(abs_spec(numbers@[i] - numbers@[j]) < threshold);
                };
                flag = true;
            }
        }
    }
    flag
}
// </vc-code>

fn main() {}
}