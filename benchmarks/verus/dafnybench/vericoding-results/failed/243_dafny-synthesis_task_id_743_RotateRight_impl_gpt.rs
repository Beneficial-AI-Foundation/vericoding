use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rotate_right(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires n >= 0,
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.index(i) == l.index((i - n + l.len() as int) % l.len() as int),
// </vc-spec>
// <vc-code>
{
    let ghost r = if l.len() == 0 {
        Seq::<int>::empty()
    } else {
        let m = l.len() as int;
        assert(m > 0);
        assert forall|i: int|
            0 <= i < l.len()
            ==> 0 <= #[trigger](((i - n + m) % m)) && #[trigger](((i - n + m) % m)) < m
        by {
            assert(m > 0);
            assert(0 <= ((i - n + m) % m));
            assert(((i - n + m) % m) < m);
        };
        Seq::<int>::new(l.len(), |i: int| l.index(((i - n + m) % m)))
    };
    r
}
// </vc-code>

fn main() {}

}