// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn sign(x: int) -> int {
    if x > 0 { 1 } else if x < 0 { -1 } else { 0 }
}

spec fn sum_of_magnitudes(arr: Seq<int>) -> int
    decreases arr.len()
{
    if arr.len() == 0 { 0 } else { abs(arr[0]) + sum_of_magnitudes(arr.subrange(1, arr.len() as int)) }
}

spec fn product_of_signs(arr: Seq<int>) -> int
    decreases arr.len()
{
    if arr.len() == 0 { 1 } else { sign(arr[0]) * product_of_signs(arr.subrange(1, arr.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
proof fn sum_of_magnitudes_append(arr: Seq<int>, i: int)
    requires 0 <= i < arr.len()
    ensures sum_of_magnitudes(arr.subrange(0, i + 1)) == sum_of_magnitudes(arr.subrange(0, i)) + abs(arr[i])
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn product_of_signs_append(arr: Seq<int>, i: int)
    requires 0 <= i < arr.len()
    ensures product_of_signs(arr.subrange(0, i + 1)) == product_of_signs(arr.subrange(0, i)) * sign(arr[i])
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-helpers>

// <vc-spec>
fn prod_signs(arr: Vec<i8>) -> (result: Option<i8>)
    ensures 
        (arr@.len() == 0) ==> (result == Option::<i8>::None) &&
        (arr@.len() > 0) ==> (result == Option::<i8>::Some((sum_of_magnitudes(arr@.map(|i: nat, x: i8| x as int)) * product_of_signs(arr@.map(|i: nat, x: i8| x as int))) as i8))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Option::<i8>::None
    // impl-end
}
// </vc-code>


}

fn main() {}