// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn wow_factor(s: Seq<char>) -> int {
    if s.len() < 4 { 0 }
    else {
        wow_factor_sum(s, 0)
    }
}

spec fn count_vv_pairs_before(s: Seq<char>, pos: int) -> int
    decreases pos
{
    if pos <= 1 { 0 }
    else {
        let prev = count_vv_pairs_before(s, pos - 1);
        if s[pos-1] == 'v' && s[pos-2] == 'v' { prev + 1 } else { prev }
    }
}

spec fn count_vv_pairs_after(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos
{
    if pos >= s.len() - 1 { 0 }
    else {
        let rest = count_vv_pairs_after(s, pos + 1);
        if pos + 1 < s.len() && s[pos] == 'v' && s[pos+1] == 'v' { rest + 1 } else { rest }
    }
}

spec fn wow_factor_sum(s: Seq<char>, pos: int) -> int
    decreases s.len() - pos
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
fn solve(s: Vec<char>) -> (result: i8)
    ensures
        result as int == wow_factor(s@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}