use vstd::prelude::*;

verus! {

spec fn set_of_seq<T>(s: Seq<T>) -> Set<T> {
    Set::new(|x: T| s.contains(x))
}

// <vc-helpers>
// no additional helpers needed
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
    let ghost s_old = a@;
    let ii: int = i as int;
    let jj: int = j as int;

    a.swap(i, j);

    proof {
        // Derive swapped indices
        assert(a@[ii] == s_old[jj]);
        assert(a@[jj] == s_old[ii]);

        // Derive that all other indices remain the same
        assert(forall|m: int|
            0 <= m < a.len() && m != ii && m != jj ==> #[trigger] a@[m] == s_old[m]
        );

        // Multiset of elements is preserved by swap
        assert(a@.to_multiset() == s_old.to_multiset());
    }
}
// </vc-code>

fn main() {}

}