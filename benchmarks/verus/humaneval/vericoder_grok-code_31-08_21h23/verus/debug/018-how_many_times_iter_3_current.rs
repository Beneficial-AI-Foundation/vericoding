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
// </vc-helpers>
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
    if string.len() < substring.len() {
        return Some(0 as u32);
    }
    
    let s: Seq<char> = string@;
    let sub: Seq<char> = substring@;
    let sub_len = substring.len();
    let str_len = string.len();

    let mut count: u64 = 0;
    let mut i: usize = 0;

    while i <= str_len - sub_len
        invariant
            count <= u32::MAX as u64,
            i <= str_len,
            (count as nat) == how_many_times(s.drop(i as int), sub),
            sub.len() >= 1 && sub_len == sub.len(),
            str_len == s.len(),
            sub == substring@,
            s == string@,
    {
        let mut matches: bool = true;
        let mut j: usize = 0;

        while j < sub_len
            invariant
                j <= sub_len,
                matches ==> (forall |k: usize| 0 <= k < j ==> string@[i + k] == substring@[k]),
        {
            if string@[i + j] != substring@[j] {
                matches = false;
            }
            j += 1;
        }

        proof {
            assert(matches == sub.is_prefix_of(s.drop(i as int)));
        }

        if matches {
            if count >= (u32::MAX as u64) {
                return None;
            }
            count += 1;
        }
        i += 1;
    }

    assert((count as nat) == how_many_times(s, sub));
    assert(i == str_len - sub_len + 1);

    if count > (u32::MAX as u64) {
        None
    } else {
        Some(count as u32)
    }
}
// </vc-code>

} // verus!
fn main() {}