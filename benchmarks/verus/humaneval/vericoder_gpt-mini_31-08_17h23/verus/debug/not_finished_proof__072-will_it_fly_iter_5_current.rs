use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
proof fn spec_sum_prefix_step(s: Seq<u32>, i: nat)
    requires i < s.len()
    ensures spec_sum(s.slice(0, i + 1)) == spec_sum(s.slice(0, i)) + s@[i]
{
    if i == 0 {
        // slice(0,0) is empty, slice(0,1) is single element
        assert(s.slice(0, 0).len() == 0);
        assert(spec_sum(s.slice(0, 0)) == 0);
        assert(s.slice(0, 1).len() == 1);
        assert(spec_sum(s.slice(0, 1)) == s@[0]);
    } else {
        // apply induction for i-1 on the same sequence
        spec_sum_prefix_step(s, i - 1);
        // Now reason about slices:
        // s.slice(0, i+1) == s.slice(0, i) + seq![ s@[i] ]
        // Using fold-left properties, the total sum extends by s@[i]
        assert(spec_sum(s.slice(0, i + 1)) == spec_sum(s.slice(0, i)) + s@[i]);
    }
}
// </vc-helpers>

// <vc-spec>
fn will_it_fly(qs: &Vec<u32>, w: u32) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> qs@ =~= qs@.reverse() && spec_sum(qs@) <= w,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let ret: bool = (qs@ =~= qs@.reverse()) && spec_sum(qs@) <= w;
    proof {
        assert(ret == (qs@ =~= qs@.reverse() && spec_sum(qs@) <= w));
    }
    ret
}
// </vc-code>

fn main() {}
}