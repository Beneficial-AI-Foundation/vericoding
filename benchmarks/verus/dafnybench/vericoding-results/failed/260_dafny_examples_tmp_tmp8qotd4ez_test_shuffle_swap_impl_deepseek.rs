use vstd::prelude::*;

verus! {

spec fn set_of_seq<T>(s: Seq<T>) -> Set<T> {
    Set::new(|x: T| s.contains(x))
}

// <vc-helpers>
proof lemma_swap_preserves_multiset<T>(a: &mut Vec<T>, i: usize, j: usize, old_a: Seq<T>)
    requires
        i < old_a.len(),
        j < old_a.len(),
        a@.len() == old_a.len(),
        a@[i as int] == old_a[j as int],
        a@[j as int] == old_a[i as int],
        forall|m: int| 0 <= m < old_a.len() && m != i && m != j ==> a@[m] == old_a[m]
    ensures
        a@.to_multiset() == old_a.to_multiset()
{
    assert forall|x: T| a@.count(x) == old_a.count(x) by {
        if x == old_a[i as int] {
            if i == j {
                assert(a@.count(x) == old_a.count(x));
            } else {
                assert(a@.count(x) == old_a.count(x));
            }
        } else if x == old_a[j as int] {
            if i == j {
                assert(a@.count(x) == old_a.count(x));
            } else {
                assert(a@.count(x) == old_a.count(x));
            }
        } else {
            assert(a@.count(x) == old_a.count(x));
        }
    };
}
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
    let old_a = a@;
    proof {
        assert(old(a)@ == old_a);
    }
    
    if i != j {
        let temp = a[i];
        a[i] = a[j];
        a[j] = temp;
    }
    
    proof {
        assert(a@.len() == old_a.len());
        assert(a@[i as int] == old_a[j as int]);
        assert(a@[j as int] == old_a[i as int]);
        assert forall|m: int| 0 <= m < old_a.len() && m != i && m != j implies a@[m] == old_a[m] by {
            assert(a@[m] == old_a[m]);
        };
        
        lemma_swap_preserves_multiset(a, i, j, old_a);
    }
}
// </vc-code>

fn main() {}

}