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
/* helper modified by LLM (iteration 5): no changes from previous version */
fn is_prefix_of_exe(s: &[char], sub: &[char]) -> (b: bool)
    ensures
        b == sub@.is_prefix_of(s@),
{
    if sub.len() > s.len() {
        return false;
    }
    let mut i = 0;
    while i < sub.len()
        invariant
            i <= sub.len(),
            sub@.subrange(0, i as int) == s@.subrange(0, i as int),
        decreases sub.len() - i
    {
        if s[i] != sub[i] {
            return false;
        }
        i = i + 1;
    }
    true
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
/* code modified by LLM (iteration 5): fixed compilation error and added proof block for postcondition */
{
    let mut count: u128 = 0;
    let mut i: usize = 0;

    while i < string.len()
        invariant
            i <= string.len(),
            count <= i as u128,
            how_many_times(string@, substring@) == count + how_many_times(string@.subrange(i as int, string.len() as int), substring@),
        decreases string.len() - i
    {
        let rest_slice = &string[i..];
        let is_prefix = is_prefix_of_exe(rest_slice, substring.as_slice());

        proof {
            let current_view = string@.subrange(i as int, string.len() as int);
            assert(rest_slice@ == current_view);

            assert(how_many_times(current_view, substring@) ==
                (if substring@.is_prefix_of(current_view) { 1 } else { 0 }) +
                how_many_times(current_view.skip(1), substring@)
            ) by {
                assert(current_view.len() > 0);
            };
        }

        if is_prefix {
            count = count + 1;
        }
        
        i = i + 1;
    }

    proof {
        let final_subrange = string@.subrange(string.len() as int, string.len() as int);
        assert(final_subrange.len() == 0);
        assert(how_many_times(final_subrange, substring@) == 0);
        assert(how_many_times(string@, substring@) == count);
    }

    if count > (u32::MAX as u128) {
        None
    } else {
        Some(count as u32)
    }
}
// </vc-code>

}
fn main() {}