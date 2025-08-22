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
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): Added proper loop invariants and decreases clause */
    while i < numbers.len()
        invariant
            forall|ii: int, jj: int| 0 <= ii && 0 <= jj && ii < i && jj < numbers.len() && ii != jj ==> abs_spec(numbers[ii] - numbers[jj]) >= threshold
        decreases numbers.len() - i
    {
        let mut j = 0;
        /* code modified by LLM (iteration 1): Added proper inner loop invariants and decreases clause */
        while j < numbers.len()
            invariant
                i < numbers.len(),
                forall|ii: int, jj: int| 0 <= ii && 0 <= jj && ii < i && jj < numbers.len() && ii != jj ==> abs_spec(numbers[ii] - numbers[jj]) >= threshold,
                forall|jj: int| 0 <= jj && jj < j && (i as int) != jj ==> abs_spec(numbers[i as int] - numbers[jj]) >= threshold
            decreases numbers.len() - j
        {
            if i != j {
                /* code modified by LLM (iteration 1): Handle arithmetic overflow by checking bounds and using spec function directly */
                let ni = numbers[i] as int;
                let nj = numbers[j] as int;
                let diff_int = ni - nj;
                
                /* code modified by LLM (iteration 1): Use spec function to avoid overflow issues */
                if abs_spec(diff_int) < threshold {
                    return true;
                }
            }
            j += 1;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): Added assertion to help prove postcondition */
    assert(forall|ii: int, jj: int| 0 <= ii && 0 <= jj && ii < numbers.len() && jj < numbers.len() && ii != jj ==> abs_spec(numbers[ii] - numbers[jj]) >= threshold);
    false
}

fn main() {}
}