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
/* helper modified by LLM (iteration 5): The helper section has no content to fix. */
// </vc-helpers>

// <vc-spec>
fn how_many_times_impl(string: Vec<char>, substring: Vec<char>) -> (opt_k: Option<u32>)

    requires
        substring.len() >= 1,

    ensures
        inner_expr_how_many_times_impl(opt_k, string, substring),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced `i as nat` and `(i + substring.len()) as nat` with `i` and `i + substring.len()` respectively. These are concrete `usize` values and should not be cast to ghost types `nat` directly within concrete code. */
{
    let mut count: u32 = 0;
    let mut i: usize = 0;

    while i + substring.len() <= string.len()
        invariant
            i <= string.len(),
            count <= u32::MAX,
            @string.subsequence(0, i).count_substring(@substring) == count,
            @string.subsequence(0, string.len()).count_substring(@substring) == count + @string.subsequence(i, string.len()).count_substring(@substring),
        decreases (string.len() - i) as int
    {
        if string.subsequence_range(i, i + substring.len()) == substring {
            if count == u32::MAX {
                return None;
            }
            count = count + 1;
            i = i + 1;
        } else {
            i = i + 1;
        }
    }
    
    Some(count)
}
// </vc-code>

}
fn main() {}