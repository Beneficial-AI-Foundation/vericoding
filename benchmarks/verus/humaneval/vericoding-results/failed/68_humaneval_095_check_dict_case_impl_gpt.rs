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
/* helper modified by LLM (iteration 5): Lemma deriving existence of a non-lower-case key from failure of the universal lower-case property */
proof fn lemma_exists_non_lower_from_not_all_lower(dict: Map<Vec<char>, Vec<char>>)
    ensures
        (!(forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@))) ==> (exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_lower_case(k@)),
{
    proof {
        assert((!(forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@))) ==> (exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_lower_case(k@)));
    }
}

/* helper modified by LLM (iteration 5): Lemma deriving existence of a non-upper-case key from failure of the universal upper-case property */
proof fn lemma_exists_non_upper_from_not_all_upper(dict: Map<Vec<char>, Vec<char>>)
    ensures
        (!(forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@))) ==> (exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_upper_case(k@)),
{
    proof {
        assert((!(forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@))) ==> (exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_upper_case(k@)));
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
    /* code modified by LLM (iteration 5): remove nat suffix and structure cases to establish existence properties */
    let all_lower: bool = forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@);
    let all_upper: bool = forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@);

    if dict.len() == 0 {
        false
    } else {
        if all_lower || all_upper {
            true
        } else {
            proof {
                lemma_exists_non_lower_from_not_all_lower(dict);
                lemma_exists_non_upper_from_not_all_upper(dict);
            }
            false
        }
    }
}
// </vc-code>


}

fn main() {}