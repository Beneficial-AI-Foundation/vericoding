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
// <vc-helpers>
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

spec fn inner_expr_how_many_times_impl(opt_k: Option<u32>, string: Vec<char>, substring: Vec<char>) -> (result:bool) {
    match opt_k {
        Some(k) => k as nat == how_many_times(string@, substring@),
        None => how_many_times(string@, substring@) > u32::MAX,
    }
}
// pure-end
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
    
    let ghost s: Seq<char> = string@;
    let ghost sub: Seq<char> = substring@;
    let sub_len = substring.len();
    let str_len = string.len();

    let mut count: u64 = 0;
    let mut i: usize = 0;

    while i <= str_len - sub_len
        invariant
            count <= u32::MAX as u64,
            i <= str_len,
            (count as nat) == how_many_times(s.skip(i as int), sub),
            sub.len() >= 1 && sub_len == sub.len() as usize,
            i as int + sub_len as int <= str_len as int,
            str_len == s.len(),
            sub == substring@,
            s == string@,
    {
        let mut matches: bool = true;
        let mut j: usize = 0;

        let ghost sub_len_int = sub_len as int;

        while j < sub_len
            invariant
                j <= sub_len,
                matches == (forall |k: usize| 0 <= k < j ==> 
                    #[trigger] string[@((i + k) as int)] == substring[@(k as int)] &&
                    string[(i + k) as usize] == string[@((i + k) as int)] &&
                    substring[k as usize] == substring[@(k as int)]
                ),
                i as int + j as int < str_len as int,
                sub.len() >= 1,
                sub_len_int == sub.len(),
        {
            if string[i + j] != substring[j] {
                matches = false;
            }
            j += 1;
        }

        proof {
            assert(matches == sub.is_prefix_of(s.skip(i as int))) by {
                if matches {
                    assert(forall |k: usize| 0 <= k < sub_len ==> 
                        #[trigger] s[i as int + k as int] == sub[k as int]
                    ) by {
                        assert(forall |k: usize| 0 <= k < sub_len ==> 
                            string[(i + k) as usize] == substring[k as usize]
                        );
                    };
                    assert(sub.is_prefix_of(s.skip(i as int)));
                } else {
                    assert(sub.is_prefix_of(s.skip(i as int)) == false);
                }
            }
        }

        if matches {
            if count >= (u32::MAX as u64) {
                return None;
            }
            count += 1;
        }
        i += 1;
    }

    proof {
        assert((count as nat) == how_many_times(s, sub));
        assert(i == str_len - sub_len + 1);
    }

    if count > (u32::MAX as u64) {
        None
    } else {
        Some(count as u32)
    }
}
// </vc-code>

} // verus!
fn main() {}