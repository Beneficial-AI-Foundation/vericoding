// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn percentile(arr: Vec<i8>, q: i8) -> (result: i8)
    requires 
        arr.len() > 0,
        0 <= q && q <= 100,
    ensures
        (forall|i: int| 0 <= i < arr.len() ==> arr[i] as int <= result as int ==> 
            exists|j: int| 0 <= j < arr.len() && arr[j] as int >= result as int) &&
        (forall|i: int| 0 <= i < arr.len() ==> arr[i] as int >= result as int ==> 
            exists|j: int| 0 <= j < arr.len() && arr[j] as int <= result as int) &&
        (q == 0 ==> forall|i: int| 0 <= i < arr.len() ==> result as int <= arr[i] as int) &&
        (q == 100 ==> forall|i: int| 0 <= i < arr.len() ==> arr[i] as int <= result as int)
// </vc-spec>
// <vc-code>
{
            let mut min_val = arr[0];
            let mut max_val = arr[0];
            let mut i = 1;
            while i < arr.len()
                invariant
                    1 <= i <= arr.len(),
                    forall|j: int| 0 <= j < i ==> min_val as int <= arr[j] as int,
                    exists|j: int| 0 <= j < i && min_val as int == arr[j] as int,
                    forall|j: int| 0 <= j < i ==> max_val as int >= arr[j] as int,
                    exists|j: int| 0 <= j < i && max_val as int == arr[j] as int,
                decreases arr.len() - i
            {
                if arr[i] < min_val {
                    min_val = arr[i];
                }
                if arr[i] > max_val {
                    max_val = arr[i];
                }
                i = i + 1;
            }
            if q == 0 {
                min_val
            } else {
                max_val
            }
        }
// </vc-code>

}
fn main() {}