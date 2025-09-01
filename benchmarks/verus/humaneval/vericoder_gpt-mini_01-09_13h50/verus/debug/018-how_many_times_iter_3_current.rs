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
// No helper functions needed for this implementation.
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
    let cap_usize: usize = u32::MAX as usize;
    let mut i: usize = 0;
    let mut count: usize = 0;

    while i < n
        invariant
            i <= n,
            (count as nat) <= (cap_usize as nat) + 1,
            ((count as nat) < (cap_usize as nat) + 1) ==> ((count as nat) + how_many_times(string@.skip(i as nat), substring@) == how_many_times(string@, substring@)),
            ((count as nat) == (cap_usize as nat) + 1) ==> ((cap_usize as nat) + 1 <= how_many_times(string@, substring@)),
    {
        if substring@.is_prefix_of(string@.skip(i as nat)) {
            if count < cap_usize + 1 {
                // count' = count + 1, need to show new equality
                proof {
                    // how_many_times on the suffix where substring is prefix
                    assert(how_many_times(string@.skip(i as nat), substring@) == 1 + how_many_times(string@.skip((i + 1) as nat), substring@));
                    // from invariant count + how_many_times(skip(i)) == total
                    assert((count as nat) + how_many_times(string@.skip(i as nat), substring@) == how_many_times(string@, substring@));
                    // combine to get (count+1) + how_many_times(skip(i+1)) == total
                    assert(((count as nat) + 1) + how_many_times(string@.skip((i + 1) as nat), substring@) == how_many_times(string@, substring@));
                }
                count = count + 1;
            } else {
                // count == cap_usize + 1 (in nat terms), keep saturated
                ()
            }
        } else {
            // not a prefix at i: how_many_times(skip(i)) == how_many_times(skip(i+1))
            proof {
                assert(how_many_times(string@.skip(i as nat), substring@) == how_many_times(string@.skip((i + 1) as nat), substring@));
                // if not saturated, maintain equality: count + how_many_times(skip(i+1)) == total
                if count < cap_usize + 1 {
                    assert((count as nat) + how_many_times(string@.skip((i + 1) as nat), substring@) == how_many_times(string@, substring@));
                }
            }
            // count unchanged
        }

        i = i + 1;
    }

    if count < cap_usize + 1 {
        // At end i == n and count < cap+1, from invariant we have equality:
        proof {
            assert((count as nat) + how_many_times(string@.skip(n as nat), substring@) == how_many_times(string@, substring@));
            assert(how_many_times(string@.skip(n as nat), substring@) == 0);
            assert((count as nat) == how_many_times(string@, substring@));
        }
        Some(count as u32)
    } else {
        // count == cap+1, invariant ensures cap+1 <= total, i.e., total > cap
        proof {
            assert((cap_usize as nat) + 1 <= how_many_times(string@, substring@));
        }
        None
    }
}
// </vc-code>

} // verus!
fn main() {}