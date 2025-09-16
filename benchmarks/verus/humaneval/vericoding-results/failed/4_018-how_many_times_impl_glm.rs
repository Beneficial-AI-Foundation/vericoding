// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn how_many_times(string: Seq<char>, substring: Seq<char>) -> (result:nat)
    decreases string.len(),
{
    if (string.len() == 0) {
        0
    } else if substring.is_prefix_of(string) {
        1 + how_many_times(string.skip(1), substring)
    } else {
        how_many_times(string.skip(1), substring)
    }
}

spec fn inner_expr_how_many_times_impl(opt_k: Option<u32>, string: Vec<char>, substring: Vec<char>) -> (result:bool) {
    match opt_k {
        Some(k) => k as nat == how_many_times(string@, substring@),
        None => how_many_times(string@, substring@) > u32::MAX,
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clauses to fix recursion */
spec fn is_prefix_of(substring: Seq<char>, string: Seq<char>) -> bool
    decreases substring.len(),
{
    if substring.len() == 0 {
        true
    } else if string.len() < substring.len() {
        false
    } else {
        substring[0] == string[0] && is_prefix_of(substring.skip(1), string.skip(1))
    }
}

/* helper modified by LLM (iteration 5): added decreases clauses to fix recursion */
spec fn has_at_least_n_occurrences(string: Seq<char>, substring: Seq<char>, n: nat) -> bool
    decreases (n, string.len()),
{
    if n == 0 {
        true
    } else if string.len() < substring.len() {
        false
    } else if is_prefix_of(substring, string) {
        has_at_least_n_occurrences(string.skip(1), substring, (n - 1) as nat)
    } else {
        has_at_least_n_occurrences(string.skip(1), substring, n)
    }
}
// </vc-helpers>

// <vc-spec>
fn how_many_times_impl(string: Vec<char>, substring: Vec<char>) -> (opt_k: Option<u32>)

    requires
        substring.len() >= 1,

    ensures
        inner_expr_how_many_times_impl(opt_k, string, substring),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed; fixed helper functions */
{
    let mut count: usize = 0;
    let mut idx = 0;
    let n = string.len();
    let m = substring.len();
    
    while idx <= n - m && count <= u32::MAX as usize
        invariant
            0 <= idx <= n,
            count <= how_many_times(string@.subrange(idx as int, n as int), substring@),
            how_many_times(string@, substring@) == count + how_many_times(string@.subrange(idx as int, n as int), substring@),
        decreases n - idx
    {
        let mut found = true;
        let mut j = 0;
        while j < m {
            if string[idx + j] != substring[j] {
                found = false;
                break;
            }
            j += 1;
        }
        if found {
            count += 1;
        }
        idx += 1;
    }
    
    if count > u32::MAX as usize {
        None
    } else {
        Some(count as u32)
    }
}
// </vc-code>

}
fn main() {}