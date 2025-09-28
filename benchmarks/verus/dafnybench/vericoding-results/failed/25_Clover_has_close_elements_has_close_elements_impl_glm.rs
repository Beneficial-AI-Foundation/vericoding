use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: int, b: int) -> int {
    if a - b < 0 { b - a } else { a - b }
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
    let n = numbers.len();
    if n < 2 {
        return false;
    }
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n,
            forall |k: nat, l: nat| k < i && l < k ==> abs_diff(numbers[k], numbers[l]) >= threshold,
    {
        let mut j: usize = 0;
        while j < i
            invariant
                j <= i,
                forall |k: nat, l: nat| k < i && l < k ==> abs_diff(numbers[k], numbers[l]) >= threshold,
                forall |l: nat| l < j ==> abs_diff(numbers[i], numbers[l]) >= threshold,
        {
            let a = numbers[i];
            let b = numbers[j];
            let diff = if a >= b { a - b } else { b - a };
            if diff < threshold {
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