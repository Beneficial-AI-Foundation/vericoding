// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_sum(xs: &Vec<i32>, start: int, len: int) -> int 
    decreases len
{
    if len <= 0 {
        0
    } else {
        xs[start] + spec_sum(xs, start + 1, len - 1)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_subarray_sum(xs: &Vec<i32>) -> (result: i32)
    ensures
        xs.len() == 0 ==> result == 0,
        xs.len() > 0 ==> (
            exists|start: int, len: int| 
                0 <= start < xs.len() && 
                1 <= len <= xs.len() - start &&
                result == spec_sum(xs, start, len) as i32
        ) &&
        (forall|start: int, len: int|
            0 <= start < xs.len() && 
            1 <= len <= xs.len() - start
            ==> spec_sum(xs, start, len) <= result as int
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Used i64 for current_sum to avoid overflow in sum calculations, updated invariants to match new type. */
    if xs.len() == 0 {
        return 0;
    }
    let mut max_sum = i32::MIN;
    let mut index = 0;
    while index < xs.len()
        invariant
            0 <= index <= xs.len(),
            max_sum <= i32::MAX,
            (forall |start: int, len: int| 0 <= start < index && 1 <= len <= index - start ==> spec_sum(xs, start, len) <= max_sum as int),
            (index > 0 ==> (exists |start: int, len: int| 0 <= start < index && 1 <= len <= index - start && max_sum as int == spec_sum(xs, start, len)))
        decreases (xs.len() as int - index as int)
    {
        let start = index;
        let mut current_sum = xs[start as usize] as i64;
        let mut len = 1;
        while len <= xs.len() - start
            invariant
                start < xs.len(),
                1 <= len <= xs.len() - start,
                current_sum == spec_sum(xs, start as int, len as int) as i64
            decreases ((xs.len() - start) as int - len as int)
        {
            if current_sum > max_sum as i64 {
                max_sum = current_sum as i32;
            }
            if len < xs.len() - start {
                current_sum += xs[start as usize + len as usize] as i64;
                len += 1;
            } else {
                break;
            }
        }
        index += 1;
    }
    max_sum
}
// </vc-code>

}
fn main() {}