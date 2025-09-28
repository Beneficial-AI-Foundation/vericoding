use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// No helpers needed for this implementation
// </vc-helpers>
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
    if l.len() == 0 {
        return Seq::<int>::empty();
    }
    let len = l.len() as int;
    let real_n = n % len;
    let mut r = Vec::<int>::new();
    for i in 0..l.len() {
        let i_int = i as int;
        assert(0 <= i_int < len);
        let orig_i = (i_int - real_n + len) % len;
        r.push(l.index(orig_i));
    }
    r.view()
}
// </vc-code>

fn main() {}

}