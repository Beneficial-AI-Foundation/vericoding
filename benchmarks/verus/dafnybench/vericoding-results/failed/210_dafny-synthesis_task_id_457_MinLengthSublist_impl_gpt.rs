use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn min_length_sublist(s: Seq<Seq<int>>) -> (min_sublist: Seq<int>)
    requires 
        s.len() > 0,
    ensures 
        s.contains(min_sublist),
        forall |sublist: Seq<int>| s.contains(sublist) ==> min_sublist.len() <= sublist.len(),
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    let mut best: nat = 0;
    let mut i: nat = 1;

    // Establish initial forall invariant hint
    proof {
        let ii = i;
        let bb = best;
        assert(ii == 1);
        assert(bb == 0);
        assert_forall_by(|j: int| {
            requires 0 <= j && j < ii;
            ensures s@[bb].len() <= s@[j].len();
            {
                assert(j == 0);
                assert(s@[bb].len() <= s@[j].len());
            }
        });
    }

    while i < n
        invariant
            1 <= i && i <= n,
            best < i,
            forall |j: int| 0 <= j && j < i ==> #[trigger] s@[best].len() <= s@[j].len()
    {
        let old_i = i;
        let old_best = best;

        // Record the old invariant with old_best and old_i so it remains available after updates
        proof {
            assert_forall_by(|j: int| {
                requires 0 <= j && j < old_i;
                ensures s@[old_best].len() <= s@[j].len();
                { }
            });
        }

        if s@[old_i].len() < s@[old_best].len() {
            best = old_i;
        }

        i = old_i + 1;

        // Re-establish the forall invariant for the new i and best
        assert_forall_by(|j: int| {
            requires 0 <= j && j < i;
            ensures s@[best].len() <= s@[j].len();
            {
                if j == old_i {
                    if s@[old_i].len() < s@[old_best].len() {
                        assert(best == old_i);
                        assert(s@[best].len() <= s@[j].len());
                    } else {
                        assert(best == old_best);
                        // From not (curr_len < best_len) we get best_len <= curr_len
                        assert(s@[best].len() <= s@[j].len());
                    }
                } else {
                    assert(j < i);
                    assert(i == old_i + 1);
                    assert(j < old_i + 1);
                    assert(j <= old_i);
                    assert(j < old_i);

                    if s@[old_i].len() < s@[old_best].len() {
                        assert(best == old_i);
                        // From old invariant: s@[old_best].len() <= s@[j].len()
                        // and s@[old_i].len() < s@[old_best].len() implies s@[old_i].len() <= s@[j].len()
                        assert(s@[old_best].len() <= s@[j].len());
                        assert(s@[best].len() <= s@[j].len());
                    } else {
                        assert(best == old_best);
                        assert(s@[best].len() <= s@[j].len());
                    }
                }
            }
        });

        // Re-establish best < i
        if s@[old_i].len() < s@[old_best].len() {
            assert(best == old_i);
            assert(best < i);
        } else {
            assert(best == old_best);
            assert(old_best < old_i);
            assert(old_i < i);
            assert(best < i);
        }
    }

    assert(i == n);
    assert(best < n);

    // Prove minimality among all elements of s
    proof {
        let nn = n;
        assert(nn == s.len());
        assert_forall_by(|sublist: Seq<int>| {
            requires s.contains(sublist);
            ensures s@[best].len() <= sublist.len();
            {
                let k: int = choose |k: int| 0 <= k && k < nn && s@[k] == sublist;
                assert(0 <= k && k < nn && s@[k] == sublist);
                assert(forall |j: int| 0 <= j && j < nn ==> s@[best].len() <= s@[j].len());
                assert(s@[best].len() <= s@[k].len());
                assert(s@[best].len() <= sublist.len());
            }
        });
    }

    s@[best]
}
// </vc-code>

fn main() {
}

}