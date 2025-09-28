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
/* helper modified by LLM (iteration 4): fixed type error by removing nat conversion in non-ghost code */
fn lemma_all_keys_lower_or_upper(dict: Map<Vec<char>, Vec<char>>)
    ensures
        (dict.len() == 0) ==> ((forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@)) || (forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@))),
        (dict.len() > 0) ==> (((forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@)) || (forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@))) <==> !((exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_lower_case(k@)) && (exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_upper_case(k@))))
{
    if dict.len() == 0 {
        assert(forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@));
    } else {
        let all_lower = forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@);
        let all_upper = forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@);
        let exists_not_lower = exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_lower_case(k@);
        let exists_not_upper = exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_upper_case(k@);
        
        if all_lower || all_upper {
            assert(!exists_not_lower || !exists_not_upper);
        } else {
            assert(exists_not_lower);
            assert(exists_not_upper);
        }
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
/* code modified by LLM (iteration 4): fixed type error by removing nat conversion in non-ghost code */
{
    if dict.len() == 0 {
        false
    } else {
        let all_lower = forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@);
        let all_upper = forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@);
        all_lower || all_upper
    }
}
// </vc-code>


}

fn main() {}