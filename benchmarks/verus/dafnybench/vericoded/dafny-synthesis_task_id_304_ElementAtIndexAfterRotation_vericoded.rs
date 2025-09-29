use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
proof fn element_at_index_after_rotation(l: Seq<int>, n: int, index: int) -> (element: int)
    requires 
        n >= 0,
        0 <= index < l.len(),
    ensures 
        element == l[((index - n + l.len() as int) % l.len() as int) as int],
// </vc-spec>
// <vc-code>
{
    let len: int = l.len() as int;
    assert(len > 0);
    let idx: int = ((index - n + len) % len) as int;
    assert(0 <= idx);
    assert(idx < len);
    l[idx]
}
// </vc-code>

fn main() {
}

}