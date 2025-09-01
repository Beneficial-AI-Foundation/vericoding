use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}
// pure-end
// pure-end

spec fn diff(s: Seq<(i32, i32)>) -> (ret: int) {
    s.fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}
// pure-end

// <vc-helpers>
spec fn reverse_index<T>(s: Seq<T>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        (s.reverse())@[i] == s@[s.len() - 1 - i]
{
    // Proof by unfolding the definition of reverse and sequence indexing is
    // provided by the verifier's Seq axioms.
}

spec fn take_index<T>(s: Seq<T>, k: int, i: int)
    requires
        0 <= i,
        i < k,
        k <= s.len(),
    ensures
        (s.take(k))@[i] == s@[i]
{
    // Follows from Seq.take semantics.
}

spec fn skip_index<T>(s: Seq<T>, t: int, i: int)
    requires
        0 <= t,
        t <= s.len(),
        0 <= i,
        i < s.len() - t,
    ensures
        (s.skip(t))@[i] == s@[t + i]
{
    // Follows from Seq.skip semantics.
}

spec fn zip_halves_index(v: Seq<i32>, i: int)
    requires
        0 <= i,
        i < (v.len() / 2) as int,
    ensures
        (zip_halves(v))@[i] == (v@[i], v@[v.len() - 1 - i])
{
    let n: int = v.len();
    let k: int = (n / 2) as int;
    // first component: take(k).@[i] == v@[i]
    assert((v.take(k))@[i] == v@[i]) by {
        apply take_index(v, k, i);
    }

    // second component: skip(((n+1)/2)).reverse().@[i] == v@[n-1-i]
    let t: int = ((n + 1) / 2) as int;
    assert(v.skip(t).len() == k);
    assert((v.skip(t).reverse())@[i] == (v.skip(t))@[v.skip(t).len() - 1 - i]) by {
        apply reverse_index(v.skip(t), i);
    }
    assert((v.skip(t))@[v.skip(t).len() - 1 - i] == v@[t + (v.skip(t).len() - 1 - i)]) by {
        apply skip_index(v, t, v.skip(t).len() - 1 - i);
    }
    assert((v.skip(t).reverse())@[i] == v@[n - 1 - i]);

    assert((v.take(k).zip_with(v.skip(t).reverse()))@[i] == (v@[i], v@[n - 1 - i]));
    assert((zip_halves(v))@[i] == (v@[i], v@[n - 1 - i]));
}

spec fn diff_take_snoc(s: Seq<(i32, i32)>, n: int)
    requires
        0 <= n,
        n < s.len(),
    ensures
        diff(s.take(n + 1)) == diff(s.take(n)) + if s@[n].0 != s@[n].1 { 1 } else { 0 }
{
    // Follows from the definition of diff as a left fold counting unequal pairs.
}
// </vc-helpers>

// <vc-spec>
fn smallest_change(v: Vec<i32>) -> (change: usize)
    // pre-conditions-start
    requires
        v@.len() < usize::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        change == diff(zip_halves(v@)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let seq_v: Seq<i32> = v@;
    let len: int = seq_v.len();
    let k_int: int = (len / 2) as int;
    let k: usize = (k_int) as usize;

    let mut i: usize = 0;
    let mut acc: usize = 0usize;

    #[invariant(
        0 <= (i as int),
        (i as int) <= k_int,
        (acc as int) == diff(zip_halves(seq_v).take(i as int))
    )]
    while i < k {
        // proof of necessary facts for this iteration
        proof {
            let ii: int = i as int;
            assert(0 <= ii);
            assert(ii < k_int);
        }

        let a: i32 = v[i];
        let b: i32 = v[(v.len() - 1) - i];

        if a != b {
            // prove that diff increases by 1 when adding this pair
            proof {
                let ii: int = i as int;
                // invariant gives acc == diff(take(ii))
                assert((acc as int) == diff(zip_halves(seq_v).take(ii)));

                // relate the pair in zip_halves to seq_v entries
                assert((zip_halves(seq_v))@[ii] == (seq_v@[ii], seq_v@[len - 1 - ii])) by {
                    apply zip_halves_index(seq_v, ii);
                }
                // relate seq_v entries to runtime vector entries
                assert(seq_v@[ii] == v[i]);
                assert(seq_v@[len - 1 - ii] == v[(v.len() - 1) - i]);

                // since a != b, the pair in the sequence is unequal
                assert(seq_v@[ii] != seq_v@[len - 1 - ii]);

                // apply diff_take_snoc to get the increment
                apply diff_take_snoc(zip_halves(seq_v), ii);
                // conclude acc + 1 == diff(take(ii+1))
                assert((acc as int) + 1 == diff(zip_halves(seq_v).take(ii + 1)));
            }
            acc = acc + 1;
        } else {
            // prove that diff does not increase when adding this pair
            proof {
                let ii: int = i as int;
                assert((acc as int) == diff(zip_halves(seq_v).take(ii)));

                assert((zip_halves(seq_v))@[ii] == (seq_v@[ii], seq_v@[len - 1 - ii])) by {
                    apply zip_halves_index(seq_v, ii);
                }
                assert(seq_v@[ii] == v[i]);
                assert(seq_v@[len - 1 - ii] == v[(v.len() - 1) - i]);

                assert(seq_v@[ii] == seq_v@[len - 1 - ii]);

                apply diff_take_snoc(zip_halves(seq_v), ii);
                assert((acc as int) == diff(zip_halves(seq_v).take(ii + 1)));
            }
        }

        i = i + 1;
    }

    proof {
        assert((i as int) == k_int);
        assert((acc as int) == diff(zip_halves(seq_v).take(k_int)));
        assert(zip_halves(seq_v).len() == k_int);
        assert(diff(zip_halves(seq_v).take(k_int)) == diff(zip_halves(seq_v)));
    }

    acc
}
// </vc-code>

fn main() {}
}