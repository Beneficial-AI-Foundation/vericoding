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
    /* code modified by LLM (iteration 5): fixed direct use of `nat` and `int` in non-ghost code */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> result@[j] == start as int + j * step as int,
    {
        // Use ghost variables for intermediate calculations involving 'int' or 'nat'
        // that are then converted to 'i8' for the actual runtime value.
        let ghost val_int: int = start as int + i as int * step as int;
        let val_i_concrete: i8 = val_int as i8; // Convert the calculated int to i8 for actual use
        result.push(val_i_concrete);
        i = i + 1;
    }

    if n > 0 && step > 0 {
        assert(start < stop);
    }
    if n > 0 && step < 0 {
        assert(start > stop);
    }

    result
}
// </vc-code>


}
fn main() {}