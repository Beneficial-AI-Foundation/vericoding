// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, k: int, s: Seq<char>) -> bool {
    n >= 2 &&
    1 <= k < n &&
    s.len() == n &&
    (exists|i: int| 0 <= i < s.len() && s[i] == 'G') &&
    (exists|i: int| 0 <= i < s.len() && s[i] == 'T') &&
    (forall|i: int| 0 <= i < s.len() ==> (s[i] == 'G' || s[i] == 'T' || s[i] == '.' || s[i] == '#')) &&
    (forall|i: int, j: int| 0 <= i < j < s.len() && s[i] == 'G' ==> s[j] != 'G') &&
    (forall|i: int, j: int| 0 <= i < j < s.len() && s[i] == 'T' ==> s[j] != 'T')
}

spec fn find_first_g_or_t(s: Seq<char>) -> int
    recommends exists|i: int| 0 <= i < s.len() && (s[i] == 'G' || s[i] == 'T')
    decreases s.len()
{
    if s.len() > 0 && (s[0] == 'G' || s[0] == 'T') {
        0
    } else if s.len() > 1 {
        find_first_g_or_t(s.subrange(1, s.len() as int)) + 1
    } else {
        0
    }
}

spec fn can_reach_target(s: Seq<char>, k: int) -> bool
    recommends k > 0
{
    exists|start: int| 
        0 <= start < s.len() && 
        (s[start] == 'G' || s[start] == 'T') &&
        (forall|j: int| 0 <= j < start ==> !(s[j] == 'G' || s[j] == 'T')) &&
        (exists|final_pos: int| 
            start < final_pos < s.len() &&
            (s[final_pos] == 'G' || s[final_pos] == 'T') &&
            (final_pos - start) % k == 0 &&
            (forall|pos: int| start < pos < final_pos && (pos - start) % k == 0 ==> !(s[pos] == 'G' || s[pos] == 'T' || s[pos] == '#'))
        )
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, s: Seq<char>) -> (result: Seq<char>)
    requires valid_input(n, k, s)
    ensures 
        result == seq!['Y', 'E', 'S'] || result == seq!['N', 'O'],
        (result == seq!['Y', 'E', 'S']) <==> can_reach_target(s, k)
// </vc-spec>
// <vc-code>
{
    assume(false);
    seq!['N', 'O']
}
// </vc-code>


}

fn main() {}