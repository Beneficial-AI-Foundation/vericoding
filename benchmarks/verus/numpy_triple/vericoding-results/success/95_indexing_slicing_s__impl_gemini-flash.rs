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
/* helper modified by LLM (iteration 2): fixed type inference for `Some(1)` in ensures clause */
fn s_default_step(start: Option<usize>, stop: Option<usize>) -> (slice_obj: Slice)
    requires
        (start.is_some() && stop.is_some()) ==> start.unwrap() <= stop.unwrap(),
    ensures
        slice_obj.start == start,
        slice_obj.stop == stop,
        slice_obj.step == Some(1usize),
        (slice_obj.start.is_some() && slice_obj.stop.is_some()) ==> slice_obj.start.unwrap() <= slice_obj.stop.unwrap(),
{
    Slice {
        start: start,
        stop: stop,
        step: Some(1),
    }
}
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
/* code modified by LLM (iteration 2): returns a Slice with provided start, stop, and step */
{
    let slice = Slice {
        start: start,
        stop: stop,
        step: step,
    };
    slice
}
// </vc-code>

}
fn main() {}