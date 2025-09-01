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
    let t = s.skip(i);
    assert(t.len() > 0);
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
    let mut acc: u32 = 0;
    let mut overflow: bool = false;

    while i < n && !overflow
        invariant
            i <= n,
            acc as nat <= orig,
            acc as nat + how_many_times(string@.skip(i), substring@) == orig,
    {
        if substring@.is_prefix_of(string@.skip(i)) {
            // Use lemma to relate how_many_times at skip(i) and skip(i+1)
            proof {
                lemma_how_many_times_step(string@, substring@, i);
            }

            if acc == u32::MAX {
                // If acc is already at max, then adding one more occurrence
                // makes the total > u32::MAX. Prove orig > u32::MAX in a proof block.
                proof {
                    // From the loop invariant:
                    assert(acc as nat + how_many_times(string@.skip(i), substring@) == orig);
                    // And by the lemma:
                    lemma_how_many_times_step(string@, substring@, i);
                    assert(how_many_times(string@.skip(i), substring@) ==
                           1 + how_many_times(string@.skip(i+1), substring@));
                    // So orig == acc as nat + 1 + ...
                    assert(orig == (acc as nat) + 1 + how_many_times(string@.skip(i+1), substring@));
                    // Thus orig > acc as nat
                    assert(orig > acc as nat);
                    // acc == u32::MAX, so orig > u32::MAX
                    assert(acc == u32::MAX);
                    // casting to nat in proof is allowed
                    assert(orig > u32::MAX as nat);
                }
                overflow = true;
            } else {
                acc = acc + 1;
                i = i + 1;
            }
        } else {
            // Non-prefix case: just advance i after applying lemma
            proof {
                lemma_how_many_times_step(string@, substring@, i);
            }
            i = i + 1;
        }
    }

    // After loop, decide return value based on whether overflow was detected.
    if overflow {
        // Prove the specification: how_many_times(string@, substring@) > u32::MAX
        proof {
            // At loop exit overflow == true, and loop invariant still holds.
            // We still have that substring@.is_prefix_of(string@.skip(i)) held
            // at the moment we set overflow = true, and i was not advanced after that.
            // Re-derive the > u32::MAX fact similarly.
            assert(acc == u32::MAX);
            assert(acc as nat + how_many_times(string@.skip(i), substring@) == orig);
            lemma_how_many_times_step(string@, substring@, i);
            assert(how_many_times(string@.skip(i), substring@) ==
                   1 + how_many_times(string@.skip(i+1), substring@));
            assert(orig == (acc as nat) + how_many_times(string@.skip(i), substring@));
            assert(orig > acc as nat);
            assert(orig > u32::MAX as nat);
        }
        None
    } else {
        // No overflow: loop must have processed all positions, so i == n
        proof {
            // From invariant: acc as nat + how_many_times(string@.skip(i), substring@) == orig
            // and i == n implies how_many_times(skip(n)) == 0
            assert(i == n);
            assert(how_many_times(string@.skip(i), substring@) == 0);
            assert(acc as nat + 0 == orig);
        }
        Some(acc)
    }
    // impl-end
}
// </vc-code>
// </vc-code>

} // verus!
fn main() {}