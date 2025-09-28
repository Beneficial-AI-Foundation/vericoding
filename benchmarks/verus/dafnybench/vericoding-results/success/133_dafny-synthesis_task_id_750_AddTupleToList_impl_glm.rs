use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let r = l.push(t);
    assert(r.len() == l.len() + 1);
    assert(r[r.len() - 1] == t);
    assert(forall|i: int| 0 <= i < l.len() ==> #[trigger] r[i] == l[i]);
    r
}
// </vc-code>

fn main() {
}

} // verus!