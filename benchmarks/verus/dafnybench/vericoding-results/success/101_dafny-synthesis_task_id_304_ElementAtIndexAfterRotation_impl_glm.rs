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
    let len = l.len() as int;
    let adjusted_index = (index - n + len) % len;
    assert(0 <= adjusted_index && adjusted_index < len);
    l[adjusted_index]
}
// </vc-code>

fn main() {
}

}