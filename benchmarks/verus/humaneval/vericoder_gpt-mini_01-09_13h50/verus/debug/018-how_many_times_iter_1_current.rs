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
    let cap: nat = u32::MAX as nat;
    let mut i: nat = 0;
    let mut count: nat = 0;

    while i < n
        invariant
            i <= n,
            count <= cap + 1,
            (count < cap + 1 ==> count + how_many_times(string@.skip(i), substring@) == how_many_times(string@, substring@)),
            (count == cap + 1 ==> cap + 1 <= how_many_times(string@, substring@)),
    {
        if substring@.is_prefix_of(string@.skip(i)) {
            if count < cap + 1 {
                // count' = count + 1, need to show new equality
                proof {
                    // how_many_times on the suffix where substring is prefix
                    assert(how_many_times(string@.skip(i), substring@) == 1 + how_many_times(string@.skip(i + 1), substring@));
                    // from invariant count + how_many_times(skip(i)) == total
                    assert(count + how_many_times(string@.skip(i), substring@) == how_many_times(string@, substring@));
                    // combine to get (count+1) + how_many_times(skip(i+1)) == total
                    assert((count + 1) + how_many_times(string@.skip(i + 1), substring@) == how_many_times(string@, substring@));
                }
                count = count + 1;
            } else {
                // count == cap + 1, we keep it saturated; invariant about cap+1 <= total still holds (total is constant)
                // no-op on count
                ()
            }
        } else {
            // not a prefix at i: how_many_times(skip(i)) == how_many_times(skip(i+1))
            proof {
                assert(how_many_times(string@.skip(i), substring@) == how_many_times(string@.skip(i + 1), substring@));
                // if not saturated, maintain equality: count + how_many_times(skip(i+1)) == total
                if count < cap + 1 {
                    assert(count + how_many_times(string@.skip(i + 1), substring@) == how_many_times(string@, substring@));
                }
            }
            // count unchanged
        }

        i = i + 1;
    }

    if count < cap + 1 {
        // At end i == n and count < cap+1, from invariant we have equality:
        proof {
            assert(count + how_many_times(string@.skip(n), substring@) == how_many_times(string@, substring@));
            assert(how_many_times(string@.skip(n), substring@) == 0);
            assert(count == how_many_times(string@, substring@));
        }
        Some(count as u32)
    } else {
        // count == cap+1, invariant ensures cap+1 <= total, i.e., total > cap
        proof {
            assert(cap + 1 <= how_many_times(string@, substring@));
        }
        None
    }
}
// </vc-code>

} // verus!
fn main() {}