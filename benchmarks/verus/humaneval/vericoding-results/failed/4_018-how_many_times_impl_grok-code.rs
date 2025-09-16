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
spec fn is_prefix_at(string: Seq<char>, substring: Seq<char>, i: int) -> bool {
    string.subrange(i, i + substring.len()) == substring
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
/* code modified by LLM (iteration 3): Introduced ghost variable ghost_i to cast i to int in ghost context, and used helper spec fn is_prefix_at for ghost prefix comparison to avoid int usage in executable code. */
{
    let mut count: u64 = 0;
    let mut i: usize = 0;
    while i + substring.len() <= string.len()
        invariant
            count as nat == how_many_times(string@.skip(i as int), substring@),
            i <= string.len(),
        decreases string.len() as int - i as int,
    {
        let ghost ghost_i = i as int;
        if is_prefix_at(string@, substring@, ghost_i) {
            count = count + 1;
        }
        i = i + 1;
    }
    let opt_k = if count > (u32::MAX as u64) {
        None
    } else {
        Some(count as u32)
    };
    opt_k
}
// </vc-code>

}
fn main() {}