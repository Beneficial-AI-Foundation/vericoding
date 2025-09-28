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
proof fn lemma_swap_maintains_multiset(s: Seq<i32>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
        i != j,
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset()
{
    let s_swap = s.update(i, s[j]).update(j, s[i]);
    assert(s_swap.to_multiset() =~= s.to_multiset());
}

proof fn lemma_subrange_update_preserves_positive(s: Seq<i32>, i: int, j: int, k: int)
    requires
        0 <= i <= k,
        0 <= j < s.len(),
        k <= s.len(),
        j >= k,
        positive(s.subrange(0, k)),
    ensures
        positive(s.update(j, s[j]).subrange(0, k))
{
    assert forall|u: int| 0 <= u < k implies #[trigger] s.update(j, s[j]).subrange(0, k)[u] == s.subrange(0, k)[u] by {
        assert(s.update(j, s[j]).subrange(0, k)[u] == s.update(j, s[j])[u]);
        assert(s.update(j, s[j])[u] == s[u]);
        assert(s[u] == s.subrange(0, k)[u]);
    }
}

proof fn lemma_subrange_update_preserves_strict_negative(s: Seq<i32>, i: int, j: int, k: int)
    requires
        0 <= k <= s.len(),
        0 <= i < s.len(),
        0 <= j < s.len(),
        i < k,
        j < k,
        forall|u: int| k <= u < s.len() ==> s[u] < 0,
    ensures
        forall|u: int| k <= u < s.update(i, s[j]).update(j, s[i]).len() ==> 
            s.update(i, s[j]).update(j, s[i])[u] < 0
{
    let s_swap = s.update(i, s[j]).update(j, s[i]);
    assert forall|u: int| k <= u < s_swap.len() implies #[trigger] s_swap[u] < 0 by {
        assert(s_swap[u] == s[u]);
    }
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
        decreases j - i,
    {
        if v[i] >= 0 {
            assert(positive(v@.subrange(0, (i + 1) as int))) by {
                assert forall|u: int| 0 <= u < (i + 1) as int implies #[trigger] v@.subrange(0, (i + 1) as int)[u] >= 0 by {
                    if u < i as int {
                        assert(v@.subrange(0, (i + 1) as int)[u] == v@.subrange(0, i as int)[u]);
                    } else {
                        assert(u == i as int);
                        assert(v@.subrange(0, (i + 1) as int)[u] == v@[i as int]);
                        assert(v@[i as int] >= 0);
                    }
                }
            }
            i = i + 1;
        } else {
            j = j - 1;
            
            let temp_i = v[i];
            let temp_j = v[j];
            
            proof {
                lemma_swap_maintains_multiset(v@, i as int, j as int);
                lemma_subrange_update_preserves_positive(v@, i as int, j as int, i as int);
                lemma_subrange_update_preserves_strict_negative(v@, i as int, j as int, (j + 1) as int);
            }
            
            v.set(i, temp_j);
            v.set(j, temp_i);
            
            assert(strict_negative(v, j, v.len())) by {
                assert forall|u: usize| j <= u < v.len() implies #[trigger] v[u as int] < 0 by {
                    if u == j {
                        assert(v[u as int] == temp_i);
                        assert(temp_i < 0);
                    } else {
                        assert(v[u as int] == old(v)[u as int]);
                    }
                }
            }
        }
    }
    
    assert(i == j);
    i
}
// </vc-code>

fn main() {}

}