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

proof fn lemma_empty_dict_false()
    ensures
        (forall|k: Vec<char>| !Map::<Vec<char>, Vec<char>>::empty().contains_key(k) ==> is_lower_case(k@)),
        (forall|k: Vec<char>| !Map::<Vec<char>, Vec<char>>::empty().contains_key(k) ==> is_upper_case(k@))
{
}

proof fn lemma_map_keys_lower_or_upper(dict: Map<Vec<char>, Vec<char>>)
    ensures
        (forall|k: Vec<char>| dict.contains_key(k) ==> is_lower_case(k@)) || (forall|k: Vec<char>| dict.contains_key(k) ==> is_upper_case(k@)) ||
        ((exists|k: Vec<char>| dict.contains_key(k) && !is_lower_case(k@)) && (exists|k: Vec<char>| dict.contains_key(k) && !is_upper_case(k@)))
{
    if forall|k: Vec<char>| dict.contains_key(k) ==> is_lower_case(k@) {
    } else if forall|k: Vec<char>| dict.contains_key(k) ==> is_upper_case(k@) {
    } else {
        assert(!forall|k: Vec<char>| dict.contains_key(k) ==> is_lower_case(k@));
        assert(!forall|k: Vec<char>| dict.contains_key(k) ==> is_upper_case(k@));
        proof {
            let k1 = choose|k: Vec<char>| dict.contains_key(k) && !is_lower_case(k@);
            let k2 = choose|k: Vec<char>| dict.contains_key(k) && !is_upper_case(k@);
        }
    }
}

/* helper modified by LLM (iteration 5): Fixed keys_ method to keys */
// </vc-helpers>

// <vc-spec>
fn check_dict_case(dict: Map<Vec<char>, Vec<char>>) -> (result: bool)
    ensures
        (dict.len() == 0) ==> !result,
        result ==> ((forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@)) || (forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@))),
        !result ==> ((dict.len() == 0) || ((exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_lower_case(k@)) && (exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_upper_case(k@))))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed keys_ to keys method */
{
    if dict.is_empty() {
        lemma_empty_dict_false();
        false
    } else {
        lemma_map_keys_lower_or_upper(dict);
        
        let mut all_lower = true;
        let mut all_upper = true;
        let mut has_non_lower = false;
        let mut has_non_upper = false;
        
        proof {
            for k in dict.keys() {
                if !is_lower_case(k@) {
                    all_lower = false;
                    has_non_lower = true;
                }
                if !is_upper_case(k@) {
                    all_upper = false;
                    has_non_upper = true;
                }
            }
        }
        
        let result = all_lower || all_upper;
        
        proof {
            if result {
                if all_lower {
                    assert forall|k: Vec<char>| dict.contains_key(k) implies is_lower_case(k@) by {
                        assert(dict.contains_key(k));
                    };
                } else {
                    assert forall|k: Vec<char>| dict.contains_key(k) implies is_upper_case(k@) by {
                        assert(dict.contains_key(k));
                    };
                }
            } else {
                assert(has_non_lower);
                assert(has_non_upper);
                assert (exists|k: Vec<char>| dict.contains_key(k) && !is_lower_case(k@)) by {
                    has_non_lower;
                };
                assert (exists|k: Vec<char>| dict.contains_key(k) && !is_upper_case(k@)) by {
                    has_non_upper;
                };
            }
        }
        
        result
    }
}
// </vc-code>


}

fn main() {}