// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn wow_factor(s: Seq<char>) -> int
    requires s.len() > 0,
    requires forall|i: int| 0 <= i < s.len() ==> (s[i] == 'v' || s[i] == 'o'),
    ensures wow_factor(s) >= 0,
{
    if s.len() < 4 { 0 }
    else {
        let n = s.len();
        wow_factor_sum(s, 0)
    }
}

spec fn count_vv_pairs_before(s: Seq<char>, pos: int) -> int
    requires 0 <= pos <= s.len(),
    requires forall|i: int| 0 <= i < s.len() ==> (s[i] == 'v' || s[i] == 'o'),
    ensures count_vv_pairs_before(s, pos) >= 0,
    decreases pos,
{
    if pos <= 1 { 0 }
    else {
        let prev = count_vv_pairs_before(s, pos - 1);
        if s[pos-1] == 'v' && s[pos-2] == 'v' { prev + 1 } else { prev }
    }
}

spec fn count_vv_pairs_after(s: Seq<char>, pos: int) -> int
    requires 0 <= pos <= s.len(),
    requires forall|i: int| 0 <= i < s.len() ==> (s[i] == 'v' || s[i] == 'o'),
    ensures count_vv_pairs_after(s, pos) >= 0,
    decreases s.len() - pos,
{
    if pos >= s.len() - 1 { 0 }
    else {
        let rest = count_vv_pairs_after(s, pos + 1);
        if pos + 1 < s.len() && s[pos] == 'v' && s[pos+1] == 'v' { rest + 1 } else { rest }
    }
}

spec fn wow_factor_sum(s: Seq<char>, pos: int) -> int
    requires 0 <= pos <= s.len(),
    requires forall|i: int| 0 <= i < s.len() ==> (s[i] == 'v' || s[i] == 'o'),
    ensures wow_factor_sum(s, pos) >= 0,
    decreases s.len() - pos,
{
    if pos >= s.len() { 0 }
    else {
        let current = if s[pos] == 'o' { 
            count_vv_pairs_before(s, pos) * count_vv_pairs_after(s, pos + 1)
        } else { 0 };
        current + wow_factor_sum(s, pos + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: Seq<char>) -> (result: int)
    requires s.len() > 0,
    requires forall|i: int| 0 <= i < s.len() ==> (s[i] == 'v' || s[i] == 'o'),
    ensures result >= 0,
    ensures result == wow_factor(s),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {}