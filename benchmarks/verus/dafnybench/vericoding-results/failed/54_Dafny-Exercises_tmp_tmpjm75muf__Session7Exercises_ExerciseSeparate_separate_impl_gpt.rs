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
    let n = v.len();
    let ghost s0 = v@;

    let mut i: usize = 0;
    let mut j: usize = 0;

    while j < n
        invariant
            v.len() == n,
            0 <= i <= j <= n,
            forall|u: int| 0 <= u < i as int ==> #[trigger] v@[u] >= 0,
            forall|u: int| i as int <= u < j as int ==> #[trigger] v@[u] < 0,
            is_permutation(v@, s0)
    {
        let xj = v[j];
        if xj >= 0 {
            let prev_i = i;
            assert(xj == v@[j as int]);
            v.swap(prev_i, j);
            // After swap, position prev_i holds the old value from j, which is xj >= 0
            i += 1;
        }
        j += 1;
    }

    assert(j >= n);
    assert(j <= n);
    assert(j == n);

    // Prove the suffix is strictly negative
    assert(forall|u: usize| i <= u < n ==> v[u as int] < 0) by {
        assert forall|u: usize| i <= u < n ==> v[u as int] < 0 by {
            if i <= u && u < n {
                assert(i as int <= u as int);
                assert(u as int < n as int);
            }
        }
    };

    // Prove the prefix is nonnegative (positive)
    let s = v@.subrange(0, i as int);
    assert(forall|u: int| 0 <= u < s.len() ==> s[u] >= 0) by {
        assert forall|u: int| 0 <= u < s.len() ==> s[u] >= 0 by {
            if 0 <= u && u < s.len() {
                assert(s.len() == i as int);
                assert(0 <= u && u < i as int);
                assert(s[u] == v@[u]);
            }
        }
    };
    assert(positive(s));

    // Permutation preserved by swaps
    assert(is_permutation(v@, s0));

    i
}
// </vc-code>

fn main() {}

}