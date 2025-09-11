// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn intersperse(numbers: Seq<int>, delimiter: int) -> (interspersed: Seq<int>)
    ensures
        interspersed.len() == if numbers.len() > 0 { 2 * numbers.len() - 1 } else { 0 },
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 0 ==> 
            interspersed[i] == numbers[i / 2],
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 1 ==>
            interspersed[i] == delimiter,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}