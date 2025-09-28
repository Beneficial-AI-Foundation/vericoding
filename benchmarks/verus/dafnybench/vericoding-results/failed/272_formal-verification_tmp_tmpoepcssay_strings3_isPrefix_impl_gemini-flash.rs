use vstd::prelude::*;

verus! {

spec fn is_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() <= str.len() && 
    pre == str.subrange(0, pre.len() as int)
}

spec fn is_not_prefix_pred(pre: Seq<char>, str: Seq<char>) -> bool {
    pre.len() > str.len() || 
    pre != str.subrange(0, pre.len() as int)
}

spec fn is_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    exists|i: int| 0 <= i <= str.len() && is_prefix_pred(sub, str.subrange(i, str.len() as int))
}

spec fn is_not_substring_pred(sub: Seq<char>, str: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= str.len() ==> is_not_prefix_pred(sub, str.subrange(i, str.len() as int))
}




spec fn have_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    exists|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k && is_substring_pred(str1.subrange(i1, j1), str2)
}

spec fn have_not_common_k_substring_pred(k: nat, str1: Seq<char>, str2: Seq<char>) -> bool {
    forall|i1: int, j1: int| 0 <= i1 <= str1.len() - k && j1 == i1 + k ==> is_not_substring_pred(str1.subrange(i1, j1), str2)
}

// <vc-helpers>
#[verifier(external_body)]
spec fn seq_to_string(s: Seq<char>) -> String {
    s.iter().collect::<String>()
}
// </vc-helpers>

// <vc-spec>
fn is_prefix(pre: Seq<char>, str: Seq<char>) -> (res: bool)
    ensures
        !res <==> is_not_prefix_pred(pre, str),
        res <==> is_prefix_pred(pre, str),
// </vc-spec>
// <vc-code>
{
    if pre.len() > str.len() {
        return false;
    }
    proof {
        if pre.len() == 0 {
            assert(is_prefix_pred(pre, str));
            assert(pre == str.subrange(0, 0)); // Vacuously true
        } else {
             assert(pre.subrange(0, pre.len() as int) == pre);
        }
    }
    // Cast to `int` is fine here because `pre.len()` is a `nat` (non-negative).
    // The `int` type is required by `subrange`.
    pre.ext_equal(str.subrange(0, pre.len() as int))
}
// </vc-code>

fn main() {
}

}