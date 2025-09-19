// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn events_overlap(event1: (u32, u32), event2: (u32, u32)) -> bool {
    let (start1, duration1) = event1;
    let (start2, duration2) = event2;
    let end1 = start1 + duration1;
    let end2 = start2 + duration2;
    /* Events overlap if one starts before the other ends (with gap requirement) */
    (start1 < end2 + 1) && (start2 < end1 + 1)
}

spec fn valid_schedule(events: Seq<(u32, u32)>, selected: Seq<bool>) -> bool {
    selected.len() == events.len() &&
    forall|i: int, j: int| 0 <= i < events.len() && 0 <= j < events.len() && i != j &&
        selected[i] && selected[j] ==> !events_overlap(events[i], events[j])
}

spec fn count_selected(selected: Seq<bool>) -> nat 
    decreases selected.len()
{
    if selected.len() == 0 {
        0 as nat
    } else {
        (if selected[0] { 1 as nat } else { 0 as nat }) + count_selected(selected.skip(1))
    }
}

fn max_stadium_events(events: Vec<(u32, u32)>) -> (result: u32)
    ensures
        result <= events.len(),
        exists|selected: Seq<bool>| valid_schedule(events@, selected) && count_selected(selected) == result,
        forall|selected: Seq<bool>| valid_schedule(events@, selected) ==> count_selected(selected) <= result
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test_events = vec![(2u32, 5u32), (9u32, 7u32), (15u32, 6u32), (9u32, 3u32)];
    // println!("{}", max_stadium_events(test_events));
}