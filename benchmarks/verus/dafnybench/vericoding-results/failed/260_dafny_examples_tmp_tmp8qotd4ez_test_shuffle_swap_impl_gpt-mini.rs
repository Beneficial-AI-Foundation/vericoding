use vstd::prelude::*;

verus! {

spec fn set_of_seq<T>(s: Seq<T>) -> Set<T> {
    Set::new(|x: T| s.contains(x))
}

// <vc-helpers>
// <vc-helpers>
// No helper lemmas required.
 // (left intentionally minimal)
 // </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap<T>(a: &mut Vec<T>, i: usize, j: usize)
    requires 
        i < old(a).len(),
        j < old(a).len(),
    ensures
        a[i as int] == old(a)[j as int],
        a[j as int] == old(a)[i as int],
        forall|m: int| 0 <= m < a.len() && m != i && m != j ==> a[m] == old(a)[m],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    if i != j {
        if i < j {
            let vi = a.remove(i);
            let vj = a.remove(j - 1);
            a.insert(i, vj);
            a.insert(j, vi);
        } else {
            let vj = a.remove(j);
            let vi = a.remove(i - 1);
            a.insert(j, vi);
            a.insert(i, vj);
        }
    }
    proof {
        assert((a@).len() == (old(a)@).len());
        if i == j {
            assert(a@ == old(a)@);
        } else if (i as int) < (j as int) {
            assert((a@)[i as int] == (old(a)@)[j as int]);
            assert((a@)[j as int] == (old(a)@)[i as int]);
            assert(forall|m: int| 0 <= m && m < (a@).len() && m != (i as int) && m != (j as int) ==>
                (a@)[m] == (old(a)@)[m]);
            assert((a@).to_multiset() == (old(a)@).to_multiset());
        } else {
            assert((a@)[i as int] == (old(a)@)[j as int]);
            assert((a@)[j as int] == (old(a)@)[i as int]);
            assert(forall|m: int| 0 <= m && m < (a@).len() && m != (i as int) && m != (j as int) ==>
                (a@)[m] == (old(a)@)[m]);
            assert((a@).to_multiset() == (old(a)@).to_multiset());
        }
    }
}
// </vc-code>

fn main() {}

}