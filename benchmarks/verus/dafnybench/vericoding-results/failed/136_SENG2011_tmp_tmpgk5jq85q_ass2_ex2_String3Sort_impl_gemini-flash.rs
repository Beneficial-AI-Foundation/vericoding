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
fn sorted_3(b: Seq<char>) -> bool
    requires b.len() == 3
{
    b.index(0) <= b.index(1) && b.index(1) <= b.index(2)
}

proof fn lemma_sorted_3_implies_sorted(b: Seq<char>)
    requires b.len() == 3, sorted_3(b)
    ensures sorted(b, 0, 3)
{
    assert(b.index(0) <= b.index(1));
    assert(b.index(1) <= b.index(2));
    assert(b.index(0) <= b.index(2)); // implied by transitivity

    assert(forall|j: int, k: int| 0 <= j < k < 3 ==> b.index(j) <= b.index(k)) by {
        if j == 0 && k == 1 {
            assert(b.index(0) <= b.index(1));
        } else if j == 0 && k == 2 {
            assert(b.index(0) <= b.index(2));
        } else if j == 1 && k == 2 {
            assert(b.index(1) <= b.index(2));
        }
    };
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
    let mut b = a;

    let original_multiset = a.to_multiset();

    if b.index(0) > b.index(1) {
        let temp = b.index(0);
        b = b.update(0, b.index(1));
        b = b.update(1, temp);
        proof {
            assert(b.to_multiset() == original_multiset);
        }
    }

    if b.index(1) > b.index(2) {
        let temp = b.index(1);
        b = b.update(1, b.index(2));
        b = b.update(2, temp);
        proof {
            assert(b.to_multiset() == original_multiset);
        }
    }

    if b.index(0) > b.index(1) {
        let temp = b.index(0);
        b = b.update(0, b.index(1));
        b = b.update(1, temp);
        proof {
            assert(b.to_multiset() == original_multiset);
        }
    }
    
    assert(b.len() == 3);
    assert(b.index(0) <= b.index(1) && b.index(1) <= b.index(2)); // This is sorted_3(b)

    proof {
        lemma_sorted_3_implies_sorted(b);
        assert(sorted(b, 0, 3));
        assert(b.to_multiset() == original_multiset);
    }

    b
}
// </vc-code>

fn main() {
}

}