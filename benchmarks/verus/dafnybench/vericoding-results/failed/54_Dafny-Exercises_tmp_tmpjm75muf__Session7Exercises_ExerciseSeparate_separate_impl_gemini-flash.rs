use vstd::prelude::*;

verus! {

spec fn strict_negative(v: &Vec<i32>, i: usize, j: usize) -> bool
    recommends 0 <= i <= j <= v.len()
{
    forall|u: usize| i <= u < j ==> v[u as int] < 0
}

spec fn positive(s: Seq<i32>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn is_permutation(s: Seq<i32>, t: Seq<i32>) -> bool {
    s.to_multiset() == t.to_multiset()
}

/**
returns an index st new array is a permutation of the old array
positive first and then strictnegative, i is the firs neg or len if not any */

// <vc-helpers>
fn swap<T>(v: &mut std::vec::Vec<T>, i: usize, j: usize)
    requires
        i < v.len(),
        j < v.len(),
    ensures
        v.len() == old(v).len(),
        v@.to_multiset() == old(v)@.to_multiset(), // Changed permutes to to_multiset() comparison
        v@.update(i as int, old(v)@[j as int]).update(j as int, old(v)@[i as int]) == old(v)@.swap(i as int, j as int),
{
    // The actual swap operation is handled by the Rust standard library's swap method.
    // The proof that this results in the specified sequence update is what the ensures clause is about.
    v.swap(i, j);
}

// Adding swap spec function for sequences as it was used in ensure clause and later in code.
spec fn swap_seq<T>(s: Seq<T>, i: int, j: int) -> Seq<T>
    recommends
        0 <= i < s.len(),
        0 <= j < s.len(),
{
    s.update(i, s[j]).update(j, s[i])
}
// </vc-helpers>

// <vc-spec>
fn separate(v: &mut Vec<i32>) -> (i: usize)
    ensures
        0 <= i <= v.len(),
        positive(v@.subrange(0, i as int)),
        strict_negative(v, i, v.len()),
        is_permutation(v@, old(v)@),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = v.len();

    while i < j
        invariant
            0 <= i <= j <= v.len(),
            positive(v@.subrange(0, i as int)),
            strict_negative(v, j, v.len()),
            is_permutation(v@, old(v)@),
    {
        if v[i] >= 0 {
            i += 1;
        } else {
            j -= 1;
            if i < j {
                let old_v_contents = v@;
                let old_i_val = v[i];
                let old_j_val = v[j];

                proof {
                    assert(
                        old_v_contents.update(i as int, old_j_val as int)
                            .update(j as int, old_i_val as int) == swap_seq(old_v_contents, i as int, j as int)
                    );
                }
                swap(v, i, j);
            }
        }
    }
    i
}
// </vc-code>

fn main() {}

}