use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn max_seq(s: Seq<i32>) -> i32
    recommends s.len() > 0
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else {
        let rest = max_seq(s.subrange(1, s.len() as int));
        if s[0] > rest { s[0] } else { rest }
    }
}
// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut max_val = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i as int <= a@.len(),
            max_val == max_seq(a@.subrange(0, i as int)),
    {
        max_val = if a[i] > max_val { a[i] } else { max_val };
        i += 1;
    }
    proof {
        assert(max_val == max_seq(a@));
    }
    max_val
}
// </vc-code>

fn main() {}
}