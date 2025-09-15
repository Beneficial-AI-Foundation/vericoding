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
/* helper modified by LLM (iteration 2): Removed the lemma that was causing compilation errors earlier and replaced it with an empty comment in the helper section to avoid errors. The helper `lemma_max_is_max_or_zero` wasn't being used anywhere. */
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
/* code modified by LLM (iteration 2): Added curly braces around the invariant to fix the compilation error. Also, added missing guarantees for `max_so_far` being greater than or equal to `current_max`. */
{
    if xs.len() == 0 {
        return 0i32;
    }

    let mut max_so_far: i32 = xs[0];
    let mut current_max: i32 = xs[0];

    let mut i: usize = 1;
    while i < xs.len()
        invariant 0 < i <= xs.len(),
        invariant {
            forall|start: int, len: int|
                0 <= start < i && 1 <= len <= i - start ==> spec_sum(xs, start, len) <= max_so_far as int
        },
        invariant current_max >= 0 ==> (max_so_far >= current_max || max_so_far >= 0),
        invariant current_max < 0 ==> max_so_far >= current_max,
        decreases xs.len() - i
    {
        // Either extend the subarray or start a new one
        // The largest subarray ending at i-1 (`current_max`) + `xs[i]`
        // Or just `xs[i]` itself if `current_max` was negative
        current_max = if current_max + xs[i] > xs[i] {
            current_max + xs[i]
        } else {
            xs[i]
        };
        
        // Update the overall maximum found so far
        if current_max > max_so_far {
            max_so_far = current_max;
        }

        i = i + 1;
    }
    max_so_far
}
// </vc-code>

}
fn main() {}