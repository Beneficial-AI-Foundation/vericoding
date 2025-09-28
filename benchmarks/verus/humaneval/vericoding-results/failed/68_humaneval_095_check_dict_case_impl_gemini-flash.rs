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
/* helper modified by LLM (iteration 5): No changes needed for helper functions, they are already correct. */
spec fn all_keys_lower_case(dict: Map<Vec<char>, Vec<char>>) -> bool {
    forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@)
}
spec fn all_keys_upper_case(dict: Map<Vec<char>, Vec<char>>) -> bool {
    forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@)
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
    /* code modified by LLM (iteration 5): The issue was that `dict.len()` returns a `usize`, which cannot be implicitly cast to `int` in Verus. We need to compare it with `0usize`. */
    let all_lower = all_keys_lower_case(dict);
    let all_upper = all_keys_upper_case(dict);

    if dict.len() == 0usize {
        false
    } else {
        all_lower || all_upper
    }
}
// </vc-code>


}

fn main() {}