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
{
    Slice {
        start: start,
        stop: stop,
        step: step,
    }
}
// </vc-code>

}
fn main() {}