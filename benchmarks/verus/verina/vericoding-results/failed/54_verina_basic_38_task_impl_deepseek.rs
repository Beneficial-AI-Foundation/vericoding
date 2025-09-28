// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn all_characters_same_helper(s: Seq<char>, i: nat, j: nat) -> (result: bool)
    requires
        i <= s.len(),
        j <= s.len(),
    ensures
        result ==> (forall|k: int| i <= k && k < j ==> s[k] == s[0]),
        !result ==> (exists|k: int| i <= k && k < j && #[trigger] s[k] != s[0]),
{
    /* helper modified by LLM (iteration 5): Fix nat to int indexing with proper bounds */
    if i >= j {
        true
    } else {
        let i_int: int = i as int;
        if i_int < s.len() as int {
            if s[i_int] != s[0] {
                false
            } else {
                all_characters_same_helper(s, i+1, j)
            }
        } else {
            true
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn all_characters_same(s: Seq<char>) -> (result: bool)
    requires true,
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 0 && exists|i: int| 0 <= i < s.len() && #[trigger] s[i] != s[0]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix nat/integer type mismatches in comparisons */
    if s.len() as int == 0 {
        true
    } else {
        proof {
            let helper_result = all_characters_same_helper(s, 0, s.len() as nat);
            assert(helper_result ==> (forall|k: int| 0 <= k && k < s.len() ==> s[k] == s[0]));
            assert(!helper_result ==> (exists|k: int| 0 <= k && k < s.len() && s[k] != s[0]));
        }
        let helper_result = all_characters_same_helper(s, 0, s.len() as nat);
        helper_result
    }
}
// </vc-code>

}
fn main() {}