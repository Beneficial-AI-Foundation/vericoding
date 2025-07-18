use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

fn abs(i: i32) -> (res: i32)
    requires
        i != i32::MIN,
    ensures
        i < 0 ==> res == -i,
        i >= 0 ==> res == i
{
    if i < 0 {
        -i
    } else {
        i
    }
}

#[verifier::loop_isolation(false)]
fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // pre-conditions-start
    requires
        threshold > 0,
        forall|i: int, j: int| 0 <= i && i < numbers.len() && 0 <= j && j < numbers.len() ==> numbers[i] - numbers[j] < i32::MAX && -(numbers[i] - numbers[j]) < i32::MAX
    // pre-conditions-end
    // post-conditions-start
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): moved requires/ensures clauses before function body and implemented the function logic */
    let mut i = 0;
    while i < numbers.len()
        invariant
            forall|ii: int, jj: int| 0 <= ii && ii < i && 0 <= jj && jj < numbers.len() && ii != jj ==> abs_spec(numbers[ii] - numbers[jj]) >= threshold
    {
        let mut j = 0;
        while j < numbers.len()
            invariant
                i < numbers.len(),
                forall|ii: int, jj: int| 0 <= ii && ii < i && 0 <= jj && jj < numbers.len() && ii != jj ==> abs_spec(numbers[ii] - numbers[jj]) >= threshold,
                forall|jj: int| 0 <= jj && jj < j && i != jj ==> abs_spec(numbers[i] - numbers[jj]) >= threshold
        {
            if i != j {
                let diff = numbers[i] - numbers[j];
                let abs_diff = abs_spec(diff);
                if abs_diff < threshold {
                    return true;
                }
            }
            j += 1;
        }
        i += 1;
    }
    false
}

fn main() {}
}