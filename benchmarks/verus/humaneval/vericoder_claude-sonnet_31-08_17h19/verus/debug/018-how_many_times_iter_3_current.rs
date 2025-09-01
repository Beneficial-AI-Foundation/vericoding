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
proof fn how_many_times_bounded_by_string_len(string: Seq<char>, substring: Seq<char>)
    requires substring.len() >= 1
    ensures how_many_times(string, substring) <= string.len()
    decreases string.len()
{
    if string.len() == 0 {
    } else if substring.is_prefix_of(string) {
        how_many_times_bounded_by_string_len(string.skip(1), substring);
    } else {
        how_many_times_bounded_by_string_len(string.skip(1), substring);
    }
}

proof fn how_many_times_skip_preserves_bound(string: Seq<char>, substring: Seq<char>, count: u32)
    requires 
        substring.len() >= 1,
        count as nat == how_many_times(string, substring),
        count < u32::MAX
    ensures 
        how_many_times(string.skip(1), substring) <= u32::MAX
{
    how_many_times_bounded_by_string_len(string.skip(1), substring);
    if substring.is_prefix_of(string) {
        assert(how_many_times(string, substring) == 1 + how_many_times(string.skip(1), substring));
        assert(count as nat == 1 + how_many_times(string.skip(1), substring));
        assert(how_many_times(string.skip(1), substring) == count as nat - 1);
    } else {
        assert(how_many_times(string, substring) == how_many_times(string.skip(1), substring));
        assert(how_many_times(string.skip(1), substring) == count as nat);
    }
}

proof fn substring_match_equiv(string: Seq<char>, substring: Seq<char>, i: int)
    requires 
        0 <= i,
        i + substring.len() <= string.len(),
        substring.len() > 0
    ensures 
        substring.is_prefix_of(string.skip(i)) <==> 
        string.subrange(i, i + substring.len() as int) == substring
{
}

proof fn how_many_times_extension_lemma(string: Seq<char>, substring: Seq<char>, i: int)
    requires 
        0 <= i < string.len(),
        substring.len() >= 1
    ensures 
        how_many_times(string.take(i + 1), substring) == 
        how_many_times(string.take(i), substring) + 
        (if substring.is_prefix_of(string.skip(i)) then 1 else 0)
{
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
    let mut count: u32 = 0;
    let mut i: usize = 0;
    
    while i < string.len()
        invariant
            i <= string.len(),
            count as nat == how_many_times(string@.take(i as int), substring@),
            count <= u32::MAX,
        decreases string.len() - i
    {
        if i <= string.len() - substring.len() {
            let mut matches = true;
            let mut j = 0;
            
            while j < substring.len()
                invariant
                    j <= substring.len(),
                    i + j <= string.len(),
                    matches == (j == 0 || string@.subrange(i as int, (i + j) as int) == substring@.take(j as int)),
                decreases substring.len() - j
            {
                if string[i + j] != substring[j] {
                    matches = false;
                    break;
                }
                j += 1;
            }
            
            if matches && j == substring.len() {
                if count == u32::MAX {
                    proof {
                        assert(how_many_times(string@.take(i as int), substring@) == u32::MAX);
                        substring_match_equiv(string@, substring@, i as int);
                        assert(substring@.is_prefix_of(string@.skip(i as int)));
                        assert(how_many_times(string@, substring@) >= 1 + how_many_times(string@.take(i as int), substring@));
                        assert(how_many_times(string@, substring@) >= 1 + u32::MAX);
                        assert(how_many_times(string@, substring@) > u32::MAX);
                    }
                    return None;
                }
                count += 1;
                proof {
                    substring_match_equiv(string@, substring@, i as int);
                    assert(substring@.is_prefix_of(string@.skip(i as int)));
                    how_many_times_extension_lemma(string@, substring@, i as int);
                    assert(how_many_times(string@.take((i + 1) as int), substring@) == 
                           how_many_times(string@.take(i as int), substring@) + 1);
                }
            } else {
                proof {
                    if matches && j == substring.len() {
                        substring_match_equiv(string@, substring@, i as int);
                        assert(substring@.is_prefix_of(string@.skip(i as int)));
                    } else {
                        assert(!substring@.is_prefix_of(string@.skip(i as int)));
                    }
                    how_many_times_extension_lemma(string@, substring@, i as int);
                    assert(how_many_times(string@.take((i + 1) as int), substring@) == 
                           how_many_times(string@.take(i as int), substring@));
                }
            }
        } else {
            proof {
                assert(!substring@.is_prefix_of(string@.skip(i as int)));
                how_many_times_extension_lemma(string@, substring@, i as int);
                assert(how_many_times(string@.take((i + 1) as int), substring@) == 
                       how_many_times(string@.take(i as int), substring@));
            }
        }
        i += 1;
    }
    
    proof {
        assert(string@.take(i as int) == string@);
        assert(count as nat == how_many_times(string@, substring@));
    }
    
    Some(count)
}
// </vc-code>

} // verus!
fn main() {}