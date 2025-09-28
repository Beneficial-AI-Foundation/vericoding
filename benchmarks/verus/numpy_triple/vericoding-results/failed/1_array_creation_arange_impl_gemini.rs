// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn arange(start: i8, stop: i8, step: i8, n: usize) -> (result: Vec<i8>)
    requires step != 0,
    ensures
        result.len() == n,
        n == 0 ==> ((step > 0 && start >= stop) || (step < 0 && start <= stop)),
        n > 0 ==> (
            forall|i: int| 0 <= i < n ==> result@[i] == start as int + i * step as int
        ),
        n > 0 && step > 0 ==> (
            start < stop &&
            forall|i: int| 0 <= i < n ==> result@[i] < stop as int
        ),
        n > 0 && step < 0 ==> (
            start > stop &&
            forall|i: int| 0 <= i < n ==> result@[i] > stop as int
        ),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == start as int + j * step as int,
            (n > 0 && step > 0) ==> (start < stop && forall|j: int| 0 <= j < i ==> result@[j] < stop as int),
            (n > 0 && step < 0) ==> (start > stop && forall|j: int| 0 <= j < i ==> result@[j] > stop as int),
        decreases n - i
    {
        let val_int = start as int + (i as int) * (step as int);
        let val = val_int as i8;
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}