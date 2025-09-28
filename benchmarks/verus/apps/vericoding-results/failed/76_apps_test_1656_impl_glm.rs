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
/* code modified by LLM (iteration 5): fixed vec! macro initialization */
{
    let n = s.len();
    if n < 4 {
        return 0;
    }
    let mut before: Vec<i32> = Vec::new();
    before.push(0);
    if n >= 2 {
        before.push(0);
    }
    let mut i: usize = 2;
    while i < n
        invariant
            2 <= i <= n,
            before.len() == i,
            forall |j: int| 0 <= j < i ==> before@[j] == count_vv_pairs_before(s@, j),
    {
        let prev = before[i-1];
        let add = if s[i-1] == 'v' && s[i-2] == 'v' { 1 } else { 0 };
        before.push(prev + add);
        i += 1;
    }
    let mut after: Vec<i32> = Vec::new();
    let mut idx = 0;
    while idx < n
        invariant
            after.len() == idx,
            forall |i: int| 0 <= i < idx ==> after@[i] == 0,
    {
        after.push(0);
        idx += 1;
    }
    let mut j = n - 3;
    while j < n
        invariant
            0 <= j <= n-3,
            forall |k: int| j < k < n ==> after@[k] == count_vv_pairs_after(s@, k+1),
    {
        let next_val = after[j+1];
        let add = if s[j+1] == 'v' && s[j+2] == 'v' { 1 } else { 0 };
        after[j] = next_val + add;
        if j == 0 {
            break;
        }
        j -= 1;
    }
    let mut wow: i32 = 0;
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            wow == wow_factor_sum(s@, 0) - wow_factor_sum(s@, k as int),
    {
        if s[k] == 'o' {
            wow += before[k] * after[k];
        }
        k += 1;
    }
    wow as i8
}
// </vc-code>


}

fn main() {}