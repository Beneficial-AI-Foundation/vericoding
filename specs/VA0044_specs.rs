// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n >= 13 && n % 2 == 1 && s.len() == n
}

spec fn count_eights_in_prefix(s: Seq<char>, len: int) -> int
    decreases len
{
    if len == 0 {
        0
    } else {
        (if s[len-1] == '8' { 1 } else { 0 }) + count_eights_in_prefix(s, len-1)
    }
}

spec fn vasya_wins(n: int, s: Seq<char>) -> bool {
    let petya_moves = (n - 11) / 2;
    let prefix_len = n - 10;
    let eights_in_prefix = count_eights_in_prefix(s, prefix_len);
    petya_moves < eights_in_prefix
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, s: Seq<char>) -> (result: String)
    requires valid_input(n, s)
    ensures result == "NO" || result == "YES"
    ensures result == if vasya_wins(n, s) { "YES".to_string() } else { "NO".to_string() }
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "".to_string()
    // impl-end
}
// </vc-code>


}

fn main() {}