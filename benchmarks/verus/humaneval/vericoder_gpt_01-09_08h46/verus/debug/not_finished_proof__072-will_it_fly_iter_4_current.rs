use vstd::prelude::*;

verus! {

// pure-end

spec fn spec_sum(s: Seq<u32>) -> (ret:int) {
    s.fold_left(0, |x: int, y| x + y)
}
// pure-end

// <vc-helpers>
proof fn u32_le_cast_equiv(x: int, w: u32)
    ensures
        (x <= w) == (x <= w as int),
{
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
    let b = qs@ =~= qs@.reverse();
    let s = spec_sum(qs@);
    proof { u32_le_cast_equiv(s, w); }
    b && s <= (w as int)
}
// </vc-code>

fn main() {}
}