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
    while i < numbers.len()
        invariant
            forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < numbers.len() && ii != jj ==> abs_spec(numbers[ii] - numbers[jj]) >= threshold
    {
        let mut j = 0;
        while j < numbers.len()
            invariant
                forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < numbers.len() && ii != jj ==> abs_spec(numbers[ii] - numbers[jj]) >= threshold,
                forall|jj: int| 0 <= jj < j && (i as int) != jj ==> abs_spec(numbers[i as int] - numbers[jj]) >= threshold
        {
            /* code modified by LLM (iteration 1): use ghost variables and proof block to connect executable code to spec, fix type mismatches */
            if i != j {
                let ghost diff_int: int = numbers[i as int] - numbers[j as int];
                let ghost threshold_int: int = threshold as int;
                
                proof {
                    assert(abs_spec(diff_int) < threshold_int <==> abs_spec(numbers[i as int] - numbers[j as int]) < (threshold as int));
                }
                
                let diff = numbers[i] - numbers[j];
                let abs_diff = if diff < 0 { -diff } else { diff };
                
                if abs_diff < threshold {
                    proof {
                        assert(abs_spec(diff_int) < threshold_int);
                        assert(exists|ii: int, jj: int| 0 <= ii && 0 <= jj && ii < numbers.len() && jj < numbers.len() && ii != jj && abs_spec(numbers[ii] - numbers[jj]) < threshold) by {
                            assert(0 <= (i as int) && 0 <= (j as int) && (i as int) < numbers.len() && (j as int) < numbers.len() && (i as int) != (j as int) && abs_spec(numbers[i as int] - numbers[j as int]) < threshold);
                        }
                    }
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