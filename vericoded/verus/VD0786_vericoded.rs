use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
proof fn add_tuple_to_list(l: Seq<(int, int)>, t: (int, int)) -> (r: Seq<(int, int)>)
    ensures
        r.len() == l.len() + 1,
        r[r.len() - 1] == t,
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[i]
// </vc-spec>
// <vc-code>
{
    let r0 = l.push(t);
    assert(r0.len() == l.len() + 1);
    assert(r0[(l.len() as int)] == t);
    assert(r0[r0.len() - 1] == t);
    assert(forall|i: int| 0 <= i < l.len() ==> r0[i] == l[i]);
    r0
}
// </vc-code>

fn main() {
}

} // verus!