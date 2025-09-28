use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: int, b: int) -> int {
    if a < b { b - a } else { a - b }
}

proof fn has_close_elements_witness_proof(numbers: Seq<int>, threshold: int, i: int, j: int)
    requires
        0 <= i < numbers.len(),
        0 <= j < numbers.len(),
        i != j,
        abs_diff(numbers[i], numbers[j]) < threshold,
    ensures
        exists|i2: int, j2: int| 0 <= i2 < numbers.len() && 0 <= j2 < numbers.len() && i2 != j2 && 
            abs_diff(numbers[i2], numbers[j2]) < threshold,
{
}

proof fn has_close_elements_nonwitness_proof(numbers: Seq<int>, threshold: int)
    requires
        forall|i: int, j: int| 1 <= i < numbers.len() && 0 <= j < i ==> 
            abs_diff(numbers[i], numbers[j]) >= threshold,
    ensures
        forall|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j ==>
            abs_diff(numbers[i], numbers[j]) >= threshold,
{
    assert forall|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j implies 
        abs_diff(numbers[i], numbers[j]) >= threshold by {
        if i < j {
            let i2 = j;
            let j2 = i;
            assert(1 <= i2 < numbers.len() && 0 <= j2 < i2);
        } else {
            let i2 = i;
            let j2 = j;
            assert(1 <= i2 < numbers.len() && 0 <= j2 < i2);
        }
    };
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
    if numbers.len() <= 1 {
        false
    } else {
        let mut found = false;
        let mut i: usize = 0;
        while i < numbers.len()
            invariant
                0 <= i <= numbers.len(),
                found ==> exists|k: int, l: int| 0 <= k < numbers.len() && 0 <= l < numbers.len() && k != l && 
                    abs_diff(numbers[k], numbers[l]) < threshold,
                !found ==> forall|k: int, l: int| 0 <= k < i && 0 <= l < k ==> 
                    abs_diff(numbers[k], numbers[l]) >= threshold,
        {
            let mut j: usize = 0;
            while j < i
                invariant
                    0 <= j <= i,
                    found ==> exists|k: int, l: int| 0 <= k < numbers.len() && 0 <= l < numbers.len() && k != l && 
                        abs_diff(numbers[k], numbers[l]) < threshold,
                    !found ==> forall|k: int, l: int| 0 <= k < i && 0 <= l < k ==> 
                        abs_diff(numbers[k], numbers[l]) >= threshold,
                    !found ==> forall|l: usize| 0 <= l < j ==> 
                        abs_diff(numbers[i], numbers[l]) >= threshold,
            {
                if abs_diff(numbers[i], numbers[j]) < threshold {
                    proof { has_close_elements_witness_proof(numbers, threshold, i as int, j as int); }
                    found = true;
                    j = i;
                } else {
                    j += 1;
                }
            }
            i += 1;
        }
        
        if !found {
            proof { has_close_elements_nonwitness_proof(numbers, threshold); }
        }
        
        found
    }
}
// </vc-code>

fn main() {
}

}