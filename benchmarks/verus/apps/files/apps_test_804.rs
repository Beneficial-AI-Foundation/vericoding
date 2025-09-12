// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>, k: int) -> bool {
    1 <= k <= 26 && 1 <= s.len() <= 1000 && 
    forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] <= 'z'
}

spec fn unique_chars(s: Seq<char>) -> Set<char> {
    s.to_set()
}

spec fn min_changes(s: Seq<char>, k: int) -> int
    requires valid_input(s, k) && s.len() >= k
{
    let unique = unique_chars(s);
    if k <= unique.len() { 0 } else { k - unique.len() }
}

spec fn is_impossible(s: Seq<char>, k: int) -> bool
    requires valid_input(s, k)
{
    s.len() < k
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: Seq<char>, k: int) -> (result: String)
    requires valid_input(s, k)
    ensures is_impossible(s, k) ==> result == "impossible"
    ensures !is_impossible(s, k) ==> result == min_changes(s, k).to_string()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}