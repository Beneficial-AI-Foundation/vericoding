use vstd::prelude::*;

verus! {

// <vc-helpers>
#[trigger] fn in_set(j: int, a: Seq<int>, b: Seq<int>, c: Seq<int>) -> bool {
      let n = a.len();
      0 <= j < n as int && a.index(j as usize) == b.index(j as usize) && b.index(j as usize) == c.index(j as usize)
}
// </vc-helpers>

// <vc-spec>
fn count_identical_positions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: usize)
    requires
        a.len() == b.len() && b.len() == c.len(),
    ensures
        count >= 0,
        count == Set::<int>::new(|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len(),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: int = 0;
    let mut cnt: usize = 0;
    while i < n as int
        invariant
            0 <= i <= n as int,
            cnt as int == ({
                let s = Set::<int>::new(|j: int| in_set(j, a, b, c));
                s.len()
            }),
    {
        if a.index(i as usize) == b.index(i as usize) && b.index(i as usize) == c.index(i as usize) {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}
// </vc-code>

fn main() {
}

}