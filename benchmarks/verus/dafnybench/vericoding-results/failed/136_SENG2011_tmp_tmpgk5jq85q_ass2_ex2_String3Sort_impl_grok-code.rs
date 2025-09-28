use vstd::prelude::*;

verus! {

// verifies
// check that string between indexes low and high-1 are sorted
spec fn sorted(a: Seq<char>, low: int, high: int) -> bool
    recommends 0 <= low <= high <= a.len()
{ 
    forall|j: int, k: int| low <= j < k < high ==> a[j] <= a[k]
}

// <vc-helpers>
spec fn min3(x: char, y: char, z: char) -> char {
    if x <= y {
        if x <= z { x } else { z }
    } else {
        if y <= z { y } else { z }
    }
}

spec fn max3(x: char, y: char, z: char) -> char {
    if x >= y {
        if x >= z { x } else { z }
    } else {
        if y >= z { y } else { z }
    }
}

spec fn middle3(x: char, y: char, z: char) -> char {
    let mn = min3(x, y, z);
    let mx = max3(x, y, z);
    if x != mn && x != mx { x }
    else if y != mn && y != mx { y }
    else { z }
}

fn min3_le(x: char, y: char, z: char, a: char)
    requires
        a == x || a == y || a == z
    ensures
        min3(x, y, z) <= a
{
    let mn = min3(x, y, z);
    if a == x {
        assert(mn <= x);
    } else if a == y {
        assert(mn <= y);
    } else if a == z {
        assert(mn <= z);
    }
}

fn max3_ge(x: char, y: char, z: char, a: char)
    requires
        a == x || a == y || a == z
    ensures
        a <= max3(x, y, z)
{
    let mx = max3(x, y, z);
    if a == x {
        assert(mx >= x);
    } else if a == y {
        assert(mx >= y);
    } else if a == z {
        assert(mx >= z);
    }
}
// </vc-helpers>

// <vc-spec>
fn string3_sort(a: Seq<char>) -> (b: Seq<char>)
    requires 
        a.len() == 3,
    ensures 
        sorted(b, 0, b.len() as int),
        a.len() == b.len(),
        seq![b[0], b[1], b[2]].to_multiset() == seq![a[0], a[1], a[2]].to_multiset(),
// </vc-spec>
// <vc-code>
{
    let mn = min3(a@[0], a@[1], a@[2]);
    let mx = max3(a@[0], a@[1], a@[2]);
    let mid = middle3(a@[0], a@[1], a@[2]);
    let b = seq![mn, mid, mx];

    proof {
        assert(forall|i: int| 0 <= i < 3 ==> #[trigger] b@[i] == a@[0] || b@[i] == a@[1] || b@[i] == a@[2]);
        min3_le(a@[0], a@[1], a@[2], mid);
        assert(mn <= mid);
        max3_ge(a@[0], a@[1], a@[2], mid);
        assert(mid <= mx);
        assert(forall|j: int, k: int| 0 <= j < k < 3 ==> b@[j] <= b@[k]);
        assert(seq![b@[0], b@[1], b@[2]].to_multiset() == seq![a@[0], a@[1], a@[2]].to_multiset());
    }

    b
}
// </vc-code>

fn main() {
}

}