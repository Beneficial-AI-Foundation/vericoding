use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>
// No additional helpers needed for this implementation
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
    if n <= 1 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|i_prev: int, j_prev: int| 
                0 <= i_prev && i_prev < i && 0 <= j_prev && j_prev < n && i_prev != j_prev 
                ==> abs_spec(numbers[i_prev] - numbers[j_prev]) >= threshold,
        decreases n - i,
    {
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= i < n,
                0 <= j <= n,
                forall|i_prev: int, j_prev: int| 
                    0 <= i_prev && i_prev < i && 0 <= j_prev && j_prev < n && i_prev != j_prev 
                    ==> abs_spec(numbers[i_prev] - numbers[j_prev]) >= threshold,
                forall|j_prev: int|
                    0 <= j_prev && j_prev < j && i != j_prev
                    ==> abs_spec(numbers[i as int] - numbers[j_prev]) >= threshold,
            decreases n - j,
        {
            if i != j {
                let diff = numbers[i] - numbers[j];
                let abs_diff = if diff < 0 { -diff } else { diff };
                
                proof {
                    assert(abs_diff == abs_spec(numbers[i as int] - numbers[j as int]));
                }
                
                if abs_diff < threshold {
                    proof {
                        assert(0 <= i && i < n);
                        assert(0 <= j && j < n);
                        assert(i != j);
                        assert(abs_spec(numbers[i as int] - numbers[j as int]) < threshold);
                    }
                    return true;
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(forall|i: int, j: int| 
            0 <= i && i < n && 0 <= j && j < n && i != j 
            ==> abs_spec(numbers[i] - numbers[j]) >= threshold);
    }
    false
}
// </vc-code>

fn main() {}
}