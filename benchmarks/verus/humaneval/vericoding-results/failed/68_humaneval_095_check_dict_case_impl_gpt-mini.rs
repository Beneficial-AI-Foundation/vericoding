// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lower_case(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> ('a' <= #[trigger] s[i] <= 'z')
}

spec fn is_upper_case(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> ('A' <= #[trigger] s[i] <= 'Z')
}

type DictCase = Map<Seq<char>, Seq<char>>;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): empty sequence satisfies both case predicates */
fn empty_seq_is_both_cases(s: Seq<char>)
    requires
        s.len() == 0,
    ensures
        is_lower_case(s) && is_upper_case(s),
{
    proof {
        // For an empty sequence, the universal quantifications in is_lower_case and is_upper_case are vacuously true
        assert(forall|i: int| 0 <= i < s.len() ==> ('a' <= s[i] <= 'z'));
        assert(forall|i: int| 0 <= i < s.len() ==> ('A' <= s[i] <= 'Z'));
    }
}
// </vc-helpers>

// <vc-spec>
fn check_dict_case(dict: Map<Vec<char>, Vec<char>>) -> (result: bool)
    ensures
        (dict.len() == 0) ==> !result,
        result ==> ((forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@)) || (forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@))),
        !result ==> ((dict.len() == 0) || ((exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_lower_case(k@)) && (exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_upper_case(k@))))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute result and prove ensures */
    let result = if dict.len() == 0 {
        false
    } else {
        let all_lower = forall|k: Vec<char>| dict.contains_key(k) ==> is_lower_case(k@);
        let all_upper = forall|k: Vec<char>| dict.contains_key(k) ==> is_upper_case(k@);
        all_lower || all_upper
    };

    proof {
        // If dictionary empty, result must be false
        if dict.len() == 0 {
            assert(!result);
        } else {
            // If result true, then one of the universal properties holds by construction
            if result {
                assert((forall|k: Vec<char>| dict.contains_key(k) ==> is_lower_case(k@)) || (forall|k: Vec<char>| dict.contains_key(k) ==> is_upper_case(k@)));
            } else {
                // If result false and dict non-empty, then both universals are false, so there exist counterexamples
                if dict.len() != 0 {
                    assert(!(forall|k: Vec<char>| dict.contains_key(k) ==> is_lower_case(k@)));
                    assert(!(forall|k: Vec<char>| dict.contains_key(k) ==> is_upper_case(k@)));
                    assert(exists|k: Vec<char>| dict.contains_key(k) && !is_lower_case(k@));
                    assert(exists|k: Vec<char>| dict.contains_key(k) && !is_upper_case(k@));
                } else {
                    // covered by first branch
                    assert(dict.len() == 0);
                }
            }
        }
    }

    result
}
// </vc-code>


}

fn main() {}