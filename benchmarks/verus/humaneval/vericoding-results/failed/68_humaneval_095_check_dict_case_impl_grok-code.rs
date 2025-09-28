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
/* helper modified by LLM (iteration 5): kept spec helpers */
spec fn check_all_lower(dict: Map<Vec<char>, Vec<char>>) -> bool {
    forall |k| dict.dom().contains(k) ==> is_lower_case(k@)
}

/* helper modified by LLM (iteration 5): kept spec helpers */
spec fn check_all_upper(dict: Map<Vec<char>, Vec<char>>) -> bool {
    forall |k| dict.dom().contains(k) ==> is_upper_case(k@)
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
    /* code modified by LLM (iteration 5): fixed compilation by using len == 0 and implemented inline loop */
    if dict.len() == 0 {
        false
    } else {
        let mut all_lower = true;
        let mut all_upper = true;
        for (key, _) in dict.iter() {
            if !is_lower_case(key@) {
                all_lower = false;
            }
            if !is_upper_case(key@) {
                all_upper = false;
            }
        }
        all_lower || all_upper
    }
}
// </vc-code>


}

fn main() {}