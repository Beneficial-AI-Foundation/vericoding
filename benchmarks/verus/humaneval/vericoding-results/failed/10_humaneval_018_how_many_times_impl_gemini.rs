// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error in ensures clause by using a block expression */
proof fn lemma_set_extend_count(s_spec: Seq<char>, substr_spec: Seq<char>, i: int)
    requires
        substr_spec.len() > 0,
        0 <= i <= s_spec.len() - substr_spec.len(),
    ensures
    {
        let match_p = |k: int| 0 <= k <= s_spec.len() - substr_spec.len() && s_spec.subrange(k, k + substr_spec.len()) == substr_spec;
        let set_lt_i = Set::new(|k: int| 0 <= k < i && match_p(k));
        let set_lt_i_plus_1 = Set::new(|k: int| 0 <= k < i + 1 && match_p(k));
        if s_spec.subrange(i, i + substr_spec.len()) == substr_spec {
            set_lt_i_plus_1.len() == set_lt_i.len() + 1
        } else {
            set_lt_i_plus_1.len() == set_lt_i.len()
        }
    }
{
    let match_p = |k: int| 0 <= k <= s_spec.len() - substr_spec.len() && s_spec.subrange(k, k + substr_spec.len()) == substr_spec;
    let set_lt_i = Set::new(|k: int| 0 <= k < i && match_p(k));
    let set_lt_i_plus_1 = Set::new(|k: int| 0 <= k < i + 1 && match_p(k));

    if s_spec.subrange(i, i + substr_spec.len()) == substr_spec {
        assert(match_p(i));
        assert(!set_lt_i.contains(i));
        assert_sets_equal!(set_lt_i_plus_1, set_lt_i.insert(i));
        lemma_set_insert_len(i, set_lt_i);
    } else {
        assert(!match_p(i));
        assert_sets_equal!(set_lt_i_plus_1, set_lt_i);
    }
}
// </vc-helpers>

// <vc-spec>
fn how_many_times(s: Vec<char>, substr: Vec<char>) -> (times: usize)
    ensures times == Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes made, only helper function was fixed */
    let s_len = s.len();
    let substr_len = substr.len();

    if substr_len == 0 {
        proof {
            let expected_set = Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@);
            let target_set = Set::new(|i: int| 0 <= i <= s_len as int);
            assert_sets_equal!(expected_set, target_set);
            vstd::set_lib::lemma_int_range_len(0, s_len as int);
        }
        return s_len + 1;
    }

    if substr_len > s_len {
        proof {
            let expected_set = Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@);
            assert((s@.len() - substr@.len()) < 0);
            assert_sets_equal!(expected_set, Set::<int>::empty());
        }
        return 0;
    }

    let mut i: usize = 0;
    let mut times: usize = 0;

    let match_p = |k: int| 0 <= k <= s_len - substr_len && s@.subrange(k, k + substr_len) == substr@;
    let set_of_matches_lt_n = |n: int| Set::new(|k: int| 0 <= k < n && match_p(k));

    while i <= s_len - substr_len
        invariant
            0 <= i <= s_len - substr_len + 1,
            substr_len > 0,
            substr_len <= s_len,
            times == set_of_matches_lt_n(i as int).len(),
            s@ == s.view(),
            substr@ == substr.view(),
        decreases s_len - substr_len - i
    {
        let sub = s.subslice(i, i + substr_len);
        lemma_set_extend_count(s@, substr@, i as int);
        
        if sub == substr {
            times = times + 1;
        } else {
        }
        i = i + 1;
    }

    proof {
        let final_bound = (s_len - substr_len + 1) as int;
        let expected_set = Set::new(|i: int| 0 <= i <= s_len - substr_len && match_p(i));
        let final_set_from_loop = set_of_matches_lt_n(final_bound);
        assert_sets_equal!(final_set_from_loop, expected_set);
    }
    
    times
}
// </vc-code>


}

fn main() {}