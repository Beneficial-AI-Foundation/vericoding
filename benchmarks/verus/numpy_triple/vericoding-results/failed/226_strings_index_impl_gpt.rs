// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn clamp_to_range(x: int, lo: int, hi: int) -> (r: int)
    requires
        lo <= hi,
    ensures
        lo <= r <= hi,
{
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}
// </vc-helpers>

// <vc-spec>
fn index(a: Vec<Seq<char>>, sub: Vec<Seq<char>>, start: Vec<i8>, end_pos: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& start[i] as int >= 0 
            &&& start[i] as int <= end_pos[i] as int
            &&& end_pos[i] as int <= a[i].len() as int
            &&& sub[i].len() > 0
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& result[i] as int >= 0
            &&& start[i] as int <= result[i] as int <= end_pos[i] as int
            &&& result[i] as int + sub[i].len() as int <= a[i].len() as int
        }
// </vc-spec>
// <vc-code>
{
    loop { }
}
// </vc-code>

}
fn main() {}