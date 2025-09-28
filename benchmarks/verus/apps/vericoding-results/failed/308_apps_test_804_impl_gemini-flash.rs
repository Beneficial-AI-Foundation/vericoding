// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>, k: int) -> bool {
    1 <= k <= 26 && 1 <= s.len() <= 1000 && 
    forall|i: int| 0 <= i < s.len() ==> 'a' <= #[trigger] s[i] <= 'z'
}

spec fn unique_chars(s: Seq<char>) -> Set<char> {
    s.to_set()
}

spec fn min_changes(s: Seq<char>, k: int) -> int {
    let unique = unique_chars(s);
    if k <= unique.len() { 0 } else { k - unique.len() }
}

spec fn is_impossible(s: Seq<char>, k: int) -> bool {
    s.len() < k
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No helpers needed as solve implementation changed. */

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8) -> (result: String)
    requires valid_input(s@, k as int)
// </vc-spec>
// <vc-code>
{
    let s_seq = s@;
    let k_int = k as int;

    if is_impossible(s_seq, k_int) {
        "impossible".to_string()
    } else {
        let needed_changes = min_changes(s_seq, k_int);
        format!("{}", needed_changes)
    }
}
// </vc-code>


}

fn main() {}