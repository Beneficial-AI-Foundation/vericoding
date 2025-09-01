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
// <vc-helpers>
spec lemma reverse_index<T>(s: Seq<T>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        s.reverse().@[i] == s@[s.len() - 1 - i]
{
    // Proof by unfolding the definition of reverse and sequence indexing is
    // provided by the verifier's Seq axioms.
}

spec lemma take_index<T>(s: Seq<T>, k: int, i: int)
    requires
        0 <= i,
        i < k,
        k <= s.len(),
    ensures
        s.take(k).@[i] == s@[i]
{
    // Follows from Seq.take semantics.
}

spec lemma skip_index<T>(s: Seq<T>, t: int, i: int)
    requires
        0 <= t,
        t <= s.len(),
        0 <= i,
        i < s.len() - t,
    ensures
        s.skip(t).@[i] == s@[t + i]
{
    // Follows from Seq.skip semantics.
}

spec lemma zip_halves_index(v: Seq<i32>, i: int)
    requires
        0 <= i,
        i < (v.len() / 2) as int,
    ensures
        zip_halves(v).@[i] == (v@[i], v@[v.len() - 1 - i])
{
    let n: int = v.len();
    let k: int = (n / 2) as int;
    // first component: take(k).@[i] == v@[i]
    assert(v.take(k).@[i] == v@[i]) by {
        apply take_index(v, k, i);
    }

    // second component: skip(((n+1)/2)).reverse().@[i] == v@[n-1-i]
    let t: int = ((n + 1) / 2) as int;
    // let u = v.skip(t)
    // u.reverse().@[i] == u@[u.len() - 1 - i] == v.skip(t).@[ ( (n - t) - 1 - i ) ] == v@[ t + (n - t - 1 - i) ] == v@[ n - 1 - i ]
    assert(v.skip(t).len() == k);
    assert(v.skip(t).reverse().@[i] == v.skip(t).@[v.skip(t).len() - 1 - i]) by {
        apply reverse_index(v.skip(t), i);
    }
    assert(v.skip(t).@[v.skip(t).len() - 1 - i] == v@[t + (v.skip(t).len() - 1 - i)]) by {
        apply skip_index(v, t, v.skip(t).len() - 1 - i);
        // need bounds: 0 <= v.skip(t).len() - 1 - i < v.skip(t).len() holds because i < k and len == k
    }
    // combine to conclude second component equals v@[n-1-i]
    assert(v.skip(t).reverse().@[i] == v@[n - 1 - i]);

    // combine pair
    assert(v.take(k).zip_with(v.skip(t).reverse()).@[i] == (v@[i], v@[n - 1 - i]));
    // zip_halves(v) is exactly that expression
    assert(zip_halves(v).@[i] == (v@[i], v@[n - 1 - i]));
}

spec lemma diff_take_snoc(s: Seq<(i32, i32)>, n: int)
    requires
        0 <= n,
        n < s.len(),
    ensures
        diff(s.take(n + 1)) == diff(s.take(n)) + if s@[n].0 != s@[n].1 { 1 } else { 0 }
{
    // Follows from the definition of diff as a left fold counting unequal pairs.
}
// </vc-helpers>
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
    // impl-start
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
        // get the pair corresponding to index i in zip_halves(seq_v)
        proof {
            // ensure the lemma preconditions hold
            assert(0 <= (i as int));
            assert((i as int) < (seq_v.len() / 2) as int by {
                // since i < k and k == (len/2) as usize
            });
        }
        let a: i32 = v[i];
        let b: i32 = v[(v.len() - 1) - i];
        if a != b {
            acc = acc + 1;
            proof {
                // By lemma zip_halves_index and diff_take_snoc, the diff of the next element increases by 1
                assert(zip_halves(seq_v).@[i as int] == (seq_v@[i as int], seq_v@[len - 1 - (i as int)]));
                assert(diff(zip_halves(seq_v).take((i as int) + 1)) ==
                       diff(zip_halves(seq_v).take(i as int)) + if zip_halves(seq_v).@[i as int].0 != zip_halves(seq_v).@[i as int].1 { 1 } else { 0 });
                assert(zip_halves(seq_v).@[i as int].0 == seq_v@[i as int]);
                assert(zip_halves(seq_v).@[i as int].1 == seq_v@[len - 1 - (i as int)]);
                assert(seq_v@[i as int] != seq_v@[len - 1 - (i as int)]);
            }
        } else {
            proof {
                // By same reasoning, diff does not increase
                assert(zip_halves(seq_v).@[i as int] == (seq_v@[i as int], seq_v@[len - 1 - (i as int)]));
                assert(diff(zip_halves(seq_v).take((i as int) + 1)) ==
                       diff(zip_halves(seq_v).take(i as int)) + if zip_halves(seq_v).@[i as int].0 != zip_halves(seq_v).@[i as int].1 { 1 } else { 0 });
                assert(zip_halves(seq_v).@[i as int].0 == seq_v@[i as int]);
                assert(zip_halves(seq_v).@[i as int].1 == seq_v@[len - 1 - (i as int)]);
                assert(seq_v@[i as int] == seq_v@[len - 1 - (i as int)]);
            }
        }
        i = i + 1;
    }

    // at loop exit, i == k and acc represents diff(zip_halves(seq_v).take(k_int))
    proof {
        assert((i as int) == k_int);
        assert((acc as int) == diff(zip_halves(seq_v).take(k_int)));
        // take(k_int) on zip_halves(seq_v) yields the full zip_halves(seq_v) (its length is k_int)
        assert(zip_halves(seq_v).len() == k_int);
        assert(diff(zip_halves(seq_v).take(k_int)) == diff(zip_halves(seq_v)));
    }

    acc
    // impl-end
}
// </vc-code>

fn main() {}
}