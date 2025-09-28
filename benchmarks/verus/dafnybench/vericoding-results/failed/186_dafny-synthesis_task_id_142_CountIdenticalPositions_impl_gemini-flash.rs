use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let len = a.len();
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < len
        invariant
            0 <= i && i <= len,
            count == Set::<int>::new(|j: int| 0 <= j && j < i as int && j < a.len() as int && a.index(j as nat) == b.index(j as nat) && b.index(j as nat) == c.index(j as nat)).len(),
    {
        if a.index(i as nat) == b.index(i as nat) && b.index(i as nat) == c.index(i as nat) {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>

fn main() {
}

}