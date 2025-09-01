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
proof fn lemma_how_many_times_step(s: Seq<char>, sub: Seq<char>, i: nat)
    requires
        i < s.len(),
    ensures
        how_many_times(s.skip(i), sub) ==
            if sub.is_prefix_of(s.skip(i)) {
                1 + how_many_times(s.skip((i + (1 as nat)) as int), sub)
            } else {
                how_many_times(s.skip((i + (1 as nat)) as int), sub)
            },
    decreases
        s.len() - i,
{
    let t = s.skip(i as int);
    assert(t.len() > 0);
    assert(how_many_times(t, sub) ==
        if sub.is_prefix_of(t) {
            1 + how_many_times(t.skip(1), sub)
        } else {
            how_many_times(t.skip(1), sub)
        });
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
    // impl-start
    let n: usize = string.len();
    let mut i: usize = 0;
    let mut acc: u32 = 0;
    let mut overflow: bool = false;

    while i < n && !overflow
        invariant
            i <= n,
            acc as nat <= how_many_times(string@, substring@),
            acc as nat + how_many_times(string@.skip(i as int), substring@) == how_many_times(string@, substring@),
    {
        if substring@.is_prefix_of(string@.skip(i as int)) {
            // Use lemma to relate how_many_times at skip(i) and skip(i+1)
            proof {
                // Prove lemma precondition: i < string@.len()
                assert(i < n);
                assert(string@.len() == string.len() as nat);
                assert(i as nat < string@.len());
                lemma_how_many_times_step(string@, substring@, i as nat);
            }

            if acc == u32::MAX {
                // If acc is already at max, then adding one more occurrence
                // makes the total > u32::MAX. Prove how_many_times(...) > u32::MAX in a proof block.
                proof {
                    // From the loop invariant:
                    assert(acc as nat + how_many_times(string@.skip(i as int), substring@) == how_many_times(string@, substring@));
                    // And by the lemma:
                    assert(string@.len() == string.len() as nat);
                    assert(i < n);
                    lemma_how_many_times_step(string@, substring@, i as nat);
                    assert(how_many_times(string@.skip(i as int), substring@) ==
                           1 + how_many_times(string@.skip((i + 1) as int), substring@));
                    // So how_many_times(string, substring) == acc as nat + 1 + ...
                    assert(how_many_times(string@, substring@) == (acc as nat) + 1 + how_many_times(string@.skip((i + 1) as int), substring@));
                    // Thus how_many_times(string, substring) > acc as nat
                    assert(how_many_times(string@, substring@) > acc as nat);
                    // acc == u32::MAX, so how_many_times(...) > u32::MAX
                    assert(acc == u32::MAX);
                    assert(how_many_times(string@, substring@) > u32::MAX as nat);
                }
                overflow = true;
            } else {
                acc = acc + 1;
                i = i + 1;
            }
        } else {
            // Non-prefix case: just advance i after applying lemma
            proof {
                assert(i < n);
                assert(string@.len() == string.len() as nat);
                assert(i as nat < string@.len());
                lemma_how_many_times_step(string@, substring@, i as nat);
            }
            i = i + 1;
        }
    }

    // After loop, decide return value based on whether overflow was detected.
    if overflow {
        // Prove the specification: how_many_times(string@, substring@) > u32::MAX
        proof {
            // At loop exit overflow == true, and loop invariant still holds.
            assert(acc == u32::MAX);
            assert(acc as nat + how_many_times(string@.skip(i as int), substring@) == how_many_times(string@, substring@));
            // We must have i < string.len() because overflow was set in a loop iteration when i < n
            assert(i < n);
            assert(string@.len() == string.len() as nat);
            assert(i as nat < string@.len());
            lemma_how_many_times_step(string@, substring@, i as nat);
            assert(how_many_times(string@.skip(i as int), substring@) ==
                   1 + how_many_times(string@.skip((i + 1) as int), substring@));
            assert(how_many_times(string@, substring@) == (acc as nat) + 1 + how_many_times(string@.skip((i + 1) as int), substring@));
            assert(how_many_times(string@, substring@) > acc as nat);
            assert(how_many_times(string@, substring@) > u32::MAX as nat);
        }
        None
    } else {
        // No overflow: loop must have processed all positions, so i == n
        proof {
            // From invariant: acc as nat + how_many_times(string@.skip(i), substring@) == how_many_times(string@, substring@)
            // and i == n implies how_many_times(skip(n)) == 0
            assert(i == n);
            assert(how_many_times(string@.skip(i as int), substring@) == 0);
            assert(acc as nat + 0 == how_many_times(string@, substring@));
        }
        Some(acc)
    }
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}