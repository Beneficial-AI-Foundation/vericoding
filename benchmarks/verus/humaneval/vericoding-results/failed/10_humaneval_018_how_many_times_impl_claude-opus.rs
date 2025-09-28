// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn matches_at(s: Seq<char>, substr: Seq<char>, pos: int) -> bool {
    0 <= pos <= s.len() - substr.len() && s.subrange(pos, pos + substr.len()) == substr
}

/* helper modified by LLM (iteration 5): Added proper proof for count_bounded lemma */
proof fn count_bounded(s: Seq<char>, substr: Seq<char>, i: int)
    requires
        0 <= i <= s.len() - substr.len() + 1,
        substr.len() > 0,
    ensures
        Set::new(|j: int| 0 <= j < i && matches_at(s, substr, j)).len() <= i,
{
    // The set contains indices from 0 to i-1, so at most i elements
    let match_set = Set::new(|j: int| 0 <= j < i && matches_at(s, substr, j));
    assert forall|j: int| match_set.contains(j) implies 0 <= j < i by {
        // By definition of match_set
    }
    // The set is a subset of {0, 1, ..., i-1} which has exactly i elements
    assert(match_set.len() <= i);
}
// </vc-helpers>

// <vc-spec>
fn how_many_times(s: Vec<char>, substr: Vec<char>) -> (times: usize)
    ensures times == Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed quantifier trigger issue */
    if substr.len() == 0 {
        // Empty substring matches at every position including after the last char
        proof {
            assert(s@.len() >= 0);
            assert(s@.len() + 1 <= usize::MAX);
        }
        let result = s.len() + 1;
        proof {
            assert(s@.len() - substr@.len() == s@.len());
            assert forall|i: int| 0 <= i <= s@.len() implies s@.subrange(i, i) == substr@ by {
                assert(s@.subrange(i, i).len() == 0);
                assert(substr@.len() == 0);
            }
            let positions = Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@);
            assert(positions =~= Set::new(|i: int| 0 <= i <= s@.len()));
            // The set {0, 1, ..., n} has n+1 elements
            assert forall|i: int| 0 <= i <= s@.len() implies positions.contains(i) by {}
            assert forall|i: int| positions.contains(i) implies 0 <= i <= s@.len() by {}
        }
        return result;
    }
    
    if substr.len() > s.len() {
        proof {
            assert(s@.len() - substr@.len() < 0);
            let positions = Set::new(|i: int| 0 <= i <= s@.len() - substr@.len() && s@.subrange(i, i + substr@.len()) == substr@);
            assert forall|i: int| #[trigger] positions.contains(i) implies false by {
                if positions.contains(i) {
                    assert(0 <= i <= s@.len() - substr@.len());
                    assert(s@.len() - substr@.len() < 0);
                    assert(false);
                }
            }
            assert(positions =~= Set::empty());
        }
        return 0;
    }

    let mut count: usize = 0;
    let mut i: usize = 0;
    let limit = s.len() - substr.len() + 1;
    
    proof {
        assert(Set::new(|j: int| 0 <= j < 0 && matches_at(s@, substr@, j)) =~= Set::empty());
        assert(count == 0);
    }
    
    while i < limit
        invariant
            0 <= i <= limit,
            limit == s.len() - substr.len() + 1,
            substr.len() > 0,
            substr.len() <= s.len(),
            count <= i,
            count == Set::new(|j: int| 0 <= j < i && matches_at(s@, substr@, j)).len(),
            forall|j: int| matches_at(s@, substr@, j) <==> (0 <= j <= s@.len() - substr@.len() && s@.subrange(j, j + substr@.len()) == substr@),
        decreases limit - i,
    {
        let old_count = count;
        let mut match_found = true;
        let mut j: usize = 0;
        
        while j < substr.len()
            invariant
                0 <= j <= substr.len(),
                i < limit,
                i + substr.len() <= s.len(),
                match_found ==> (forall|k: int| 0 <= k < j ==> s@[i as int + k] == substr@[k]),
                !match_found ==> (exists|k: int| 0 <= k < j && s@[i as int + k] != substr@[k]),
            decreases substr.len() - j,
        {
            if s[i + j] != substr[j] {
                match_found = false;
                j = j + 1;
            } else {
                j = j + 1;
            }
        }
        
        if match_found {
            proof {
                assert(forall|k: int| 0 <= k < substr@.len() ==> s@[i as int + k] == substr@[k]);
                assert(s@.subrange(i as int, i as int + substr@.len()) == substr@) by {
                    assert forall|k: int| 0 <= k < substr@.len() implies s@.subrange(i as int, i as int + substr@.len())[k] == substr@[k] by {
                        assert(s@.subrange(i as int, i as int + substr@.len())[k] == s@[i as int + k]);
                    }
                }
                assert(matches_at(s@, substr@, i as int));
                count_bounded(s@, substr@, (i + 1) as int);
                assert(count < i + 1);
            }
            count = count + 1;
        }
        
        i = i + 1;
        proof {
            let prev_set = Set::new(|j: int| 0 <= j < i - 1 && matches_at(s@, substr@, j));
            let curr_set = Set::new(|j: int| 0 <= j < i && matches_at(s@, substr@, j));
            assert(old_count == prev_set.len());
            if match_found {
                assert(matches_at(s@, substr@, (i - 1) as int));
                assert(curr_set =~= prev_set.insert((i - 1) as int));
                assert(count == old_count + 1);
                assert(count == curr_set.len());
            } else {
                assert(!matches_at(s@, substr@, (i - 1) as int));
                assert(curr_set =~= prev_set);
                assert(count == old_count);
                assert(count == curr_set.len());
            }
        }
    }
    
    proof {
        assert(i == limit);
        assert(limit == s.len() - substr.len() + 1);
        assert(Set::new(|j: int| 0 <= j < i && matches_at(s@, substr@, j)) =~=
               Set::new(|j: int| 0 <= j <= s@.len() - substr@.len() && matches_at(s@, substr@, j)));
        assert(Set::new(|j: int| 0 <= j <= s@.len() - substr@.len() && matches_at(s@, substr@, j)) =~=
               Set::new(|j: int| 0 <= j <= s@.len() - substr@.len() && s@.subrange(j, j + substr@.len()) == substr@));
    }
    
    count
}
// </vc-code>


}

fn main() {}