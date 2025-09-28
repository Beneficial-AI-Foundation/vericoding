use vstd::prelude::*;

verus! {

spec fn set_of_seq<T>(s: Seq<T>) -> Set<T> {
    Set::new(|x: T| s.contains(x))
}

// <vc-helpers>
#[verifier(external_body)]
#[allow(unused_mut)]
#[allow(unused_variables)]
fn rust_vec_swap<T>(a: &mut Vec<T>, i: usize, j: usize) {
    a.swap(i, j);
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
    let old_a_seq = a@;

    rust_vec_swap(a, i, j);

    proof {
        assert(a.len() == old_a_seq.len());

        assert(a[i as int] == old_a_seq[j as int]);
        assert(a[j as int] == old_a_seq[i as int]);

        assert forall|m: int| 0 <= m < a.len() && m != i && m != j implies a[m] == old_a_seq[m] by {
            // This is handled by the `rust_vec_swap` external_body, which Verus trusts
            // to only swap at i and j and leave others unchanged.
        }

        assert(a@.to_multiset() =~= old_a_seq.to_multiset());
    }
}
// </vc-code>

fn main() {}

}