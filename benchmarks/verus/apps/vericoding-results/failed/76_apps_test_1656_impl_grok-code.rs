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
/* helper modified by LLM (iteration 5): Adjusted indexing to use (pos as int + offset) as nat instead of pos - offset to resolve compilation errors with Seq indexing and type mismatches */
fn count_vv_pairs_before_exec(s: &Vec<char>, pos: int) -> (result: i64)
    requires
        0 <= pos <= s@.len()
    ensures
        result as int == count_vv_pairs_before(s@, pos)
{
    if pos <= 1 {
        0
    } else {
        let prev = count_vv_pairs_before_exec(s, pos as int - 1);
        if s@[((pos as int - 1) as nat)] == 'v' && s@[((pos as int - 2) as nat)] == 'v' {
            prev + 1
        } else {
            prev
        }
    }
}

fn count_vv_pairs_after_exec(s: &Vec<char>, pos: int) -> (result: i64)
    requires
        0 <= pos <= s@.len()
    ensures
        result as int == count_vv_pairs_after(s@, pos)
{
    if pos >= s@.len() as int - 1 {
        0
    } else {
        let rest = count_vv_pairs_after_exec(s, pos as int + 1);
        if pos as int + 1 < s@.len() as int && s@[pos as nat] == 'v' && s@[(pos as int + 1) as nat] == 'v' {
            rest + 1
        } else {
            rest
        }
    }
}

fn wow_factor_sum_exec(s: &Vec<char>, pos: int) -> (result: i64)
    requires
        0 <= pos <= s@.len()
    ensures
        result as int == wow_factor_sum(s@, pos)
{
    if pos >= s@.len() as int {
        0
    } else {
        let current = if s@[pos as nat] == 'o' {
            count_vv_pairs_before_exec(s, pos) * count_vv_pairs_after_exec(s, pos as int + 1)
        } else {
            0
        };
        current + wow_factor_sum_exec(s, pos as int + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    ensures
        result as int == wow_factor(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adjusted function call to use 0 as int explicitly */
{
    if s.len() < 4 {
        0i8
    } else {
        let res = wow_factor_sum_exec(&s, 0 as int);
        res as i8
    }
}
// </vc-code>


}

fn main() {}