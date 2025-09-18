// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct Slice {

    pub start: Option<usize>,

    pub stop: Option<usize>,

    pub step: Option<usize>,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed validate_step to be proof function */
proof fn validate_step(step: Option<usize>) -> bool { step.is_none() || step.unwrap() > 0 }

/* helper modified by LLM (iteration 2): Fixed validate_start_stop to be proof function */
proof fn validate_start_stop(start: Option<usize>, stop: Option<usize>) -> bool { start.is_none() || stop.is_none() || start.unwrap() <= stop.unwrap() }
// </vc-helpers>

// <vc-spec>
fn s_(start: Option<usize>, stop: Option<usize>, step: Option<usize>) -> (slice: Slice)
    requires 
        step.is_some() ==> step.unwrap() > 0,
        (start.is_some() && stop.is_some()) ==> start.unwrap() <= stop.unwrap(),
    ensures 
        slice.start == start,
        slice.stop == stop,
        slice.step == step,
        slice.step.is_some() ==> slice.step.unwrap() > 0,
        (slice.start.is_some() && slice.stop.is_some()) ==> slice.start.unwrap() <= slice.stop.unwrap(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Removed proof block with exec-mode calls */
{
    Slice { start, stop, step }
}
// </vc-code>

}
fn main() {}