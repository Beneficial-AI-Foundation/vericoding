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
proof fn lemma_how_many_times_step(s: Seq<char>, sub: Seq<char>, i: nat)
    requires
        i < s.len(),
    ensures
        how_many_times(s.skip(i), sub) ==
            if sub.is_prefix_of(s.skip(i)) {
                1 + how_many_times(s.skip(i+1), sub)
            } else {
                how_many_times(s.skip(i+1), sub)
            },
    decreases
        s.len() - i,
{
    // Unfold the definition by reasoning on the length of s.skip(i).
    let t = s.skip(i);
    assert(t.len() > 0);
    // By the definition of how_many_times, the equality holds.
    // The verifier accepts the unfolding of the spec function here.
    assert(how_many_times(t, sub) ==
        if sub.is_prefix_of(t) {
            1 + how_many_times(t.skip(1), sub)
        } else {
            how_many_times(t.skip(1), sub)
        });
}
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
// <vc-code>
{
    // impl-start
    let n: nat = string.len();
    let orig: nat = how_many_times(string@, substring@);

    let mut i: nat = 0;
    let mut acc: nat = 0;

    while i < n
        invariant
            i <= n,
            acc <= orig,
            acc + how_many_times(string@.skip(i), substring@) == orig,
    {
        if substring@.is_prefix_of(string@.skip(i)) {
            // Use lemma to relate how_many_times at skip(i) and skip(i+1)
            proof {
                // i < n holds, so we can apply lemma_how_many_times_step
                lemma_how_many_times_step(string@, substring@, i);
            }
            acc = acc + 1;
            i = i + 1;
        } else {
            // Similarly apply lemma to get relation for the non-prefix case
            proof {
                lemma_how_many_times_step(string@, substring@, i);
            }
            // acc unchanged
            i = i + 1;
        }
    }

    // At this point, acc == orig
    assert(acc + how_many_times(string@.skip(i), substring@) == orig);
    assert(i == n);
    assert(how_many_times(string@.skip(i), substring@) == 0);
    assert(acc == orig);

    if acc <= u32::MAX as nat {
        let k: u32 = acc as u32;
        Some(k)
    } else {
        None
    }
    // impl-end
}
// </vc-code>
// </vc-code>

} // verus!
fn main() {}