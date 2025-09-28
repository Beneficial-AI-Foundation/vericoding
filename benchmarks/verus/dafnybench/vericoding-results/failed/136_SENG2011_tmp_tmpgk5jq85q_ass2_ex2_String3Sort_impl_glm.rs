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
proof fn lemma_sort3(a: Seq<char>, b: Seq<char>)
    requires
        a.len() == 3,
        b.len() == 3,
        b[0] <= b[1],
        b[1] <= b[2],
        seq![b[0], b[1], b[2]].to_multiset() ~= seq![a[0], a[1], a[2]].to_multiset(),
    ensures
        sorted(b, 0, 3),
{
    assert(forall|j: int, k: int| 0 <= j < k < 3 ==> #[trigger] b[j] <= b[k]);
}

fn sorted3(a: Seq<char>) -> (b: Seq<char>)
    requires
        a.len() == 3,
    ensures
        sorted(b, 0, b.len() as int),
        a.len() == b.len(),
        seq![b[0], b[1], b[2]].to_multiset() ~= seq![a[0], a[1], a[2]].to_multiset(),
{
    let x0 = a[0];
    let x1 = a[1];
    let x2 = a[2];
    
    if x0 <= x1 {
        if x1 <= x2 {
            seq![x0, x1, x2]
        } else {
            if x0 <= x2 {
                seq![x0, x2, x1]
            } else {
                seq![x2, x0, x1]
            }
        }
    } else {
        if x0 <= x2 {
            seq![x1, x0, x2]
        } else {
            if x1 <= x2 {
                seq![x1, x2, x0]
            } else {
                seq![x2, x1, x0]
            }
        }
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
    let x0 = a[0];
    let x1 = a[1];
    let x2 = a[2];
    
    if x0 <= x1 {
        if x1 <= x2 {
            seq![x0, x1, x2]
        } else {
            if x0 <= x2 {
                seq![x0, x2, x1]
            } else {
                seq![x2, x0, x1]
            }
        }
    } else {
        if x0 <= x2 {
            seq![x1, x0, x2]
        } else {
            if x1 <= x2 {
                seq![x1, x2, x0]
            } else {
                seq![x2, x1, x0]
            }
        }
    }
}
// </vc-code>

fn main() {
}

}