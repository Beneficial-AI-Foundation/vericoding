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
    let n: int = numbers.len() as int;
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant forall |p: int, q: int| 1 <= p && p < i && 0 <= q && q < p ==>
            abs_diff(numbers@[p], numbers@[q]) >= threshold;
    {
        let mut j: int = 0;
        while j < i
            invariant 0 <= j && j <= i;
            invariant forall |p: int, q: int| 1 <= p && p < i && 0 <= q && q < p ==>
                abs_diff(numbers@[p], numbers@[q]) >= threshold;
            invariant forall |q: int| 0 <= q && q < j ==> abs_diff(numbers@[i], numbers@[q]) >= threshold;
        {
            if abs_diff(numbers@[i], numbers@[j]) < threshold {
                proof {
                    assert(0 <= i && i < n);
                    assert(0 <= j && j < i);
                    assert(i != j);
                    assert(abs_diff(numbers@[i], numbers@[j]) < threshold);
                    assert(exists |ii: int, jj: int|
                        ii == i && jj == j &&
                        0 <= ii && ii < n && 0 <= jj && jj < n && ii != jj &&
                        abs_diff(numbers@[ii], numbers@[jj]) < threshold);
                }
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

fn main() {
}

}