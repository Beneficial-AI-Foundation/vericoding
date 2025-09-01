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
// pure-end
// pure-end

spec fn inner_expr_how_many_times_impl(opt_k: Option<u32>, string: Vec<char>, substring: Vec<char>) -> (result:bool) {
    match opt_k {
        Some(k) => k as nat == how_many_times(string@, substring@),
        None => how_many_times(string@, substring@) > u32::MAX,
    }
}
// pure-end

// <vc-helpers>
spec fn count_up_to(string: Vec<char>, substring: Vec<char>, i: nat) -> (result:nat)
    decreases i,
{
    if i == 0 {
        0
    } else {
        let prev = count_up_to(string, substring, i - 1);
        let pos = i - 1;
        if pos <= string.len() - substring.len() && (string@.skip(pos)).is_prefix_of(substring@) {
            prev + 1
        } else {
            prev
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn how_many_times_impl(string: Vec<char>, substring: Vec<char>) -> (opt_k: Option<u32>)
    // pre-conditions-start
    requires
        substring.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_how_many_times_impl(opt_k, string, substring),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = string.len();
    let m = substring.len();
    let mut count = 0;
    let mut i = 0;
    while i <= n - m {
        invariant count == count_up_to(string, substring, i);
        if (string@.skip(i)).is_prefix_of(substring@) {
            if count == u32::MAX {
                return None;
            }
            count += 1;
        }
        i += 1;
    }
    return Some(count);
}
// </vc-code>

} // verus!
fn main() {}