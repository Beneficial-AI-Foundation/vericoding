use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn forall_push_equiv(l: &[i32], t: i32, i: int)
    requires
        0 <= i < l.len()
    ensures
        (forall|j:int| 0 <= j < i + 1 ==> #[trigger] l[j] < t)
        == ((forall|j:int| 0 <= j < i ==> #[trigger] l[j] < t) && l[i] < t)
{
    assert((forall|j:int| 0 <= j < i + 1 ==> #[trigger] l[j] < t)
            ==> ((forall|j:int| 0 <= j < i ==> #[trigger] l[j] < t) && l[i] < t));
    assert(((forall|j:int| 0 <= j < i ==> #[trigger] l[j] < t) && l[i] < t)
            ==> (forall|j:int| 0 <= j < i + 1 ==> #[trigger] l[j] < t));
}
// </vc-helpers>

// <vc-spec>
fn below_threshold(l: &[i32], t: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut ok: bool = true;
    while i < l.len()
        invariant
            i <= l.len(),
            ok == (forall|j: int| 0 <= j < i ==> #[trigger] l[j] < t)
    {
        let i_int: int = i as int;
        let ok_prev = ok;
        let vi = l[i];
        ok = ok && vi < t;
        proof {
            assert(i_int == i as int);
            assert(vi == l[i_int]);
            assert(ok == (ok_prev && vi < t));
            assert(ok_prev == (forall|j:int| 0 <= j < i_int ==> #[trigger] l[j] < t));
            assert(ok == ((forall|j:int| 0 <= j < i_int ==> #[trigger] l[j] < t) && l[i_int] < t));
            forall_push_equiv(l, t, i_int);
            assert(ok == (forall|j:int| 0 <= j < i_int + 1 ==> #[trigger] l[j] < t));
        }
        i = i + 1;
        assert(i as int == i_int + 1);
        assert(ok == (forall|j:int| 0 <= j < i as int ==> #[trigger] l[j] < t));
    }
    assert(i == l.len());
    assert(ok == (forall|j:int| 0 <= j < l.len() ==> #[trigger] l[j] < t));
    ok
}
// </vc-code>

fn main() {}
}