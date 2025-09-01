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
    let mut count: usize = 0;
    let n = v.len();
    let mid = n / 2;

    if n % 2 == 1 {
        // Odd length, middle element is not paired
        // No change needed for this element, so no `count` update.
    }

    let mut i: usize = 0;
    while i < mid
        invariant
            0 <= i && i <= mid,
            count
                == Seq::new(i, |j| {
                    if v@[j] != v@[(n - 1) - j] {
                        1
                    } else {
                        0
                    }
                })
                .fold_left(0, |acc, x| acc + x),
    {
        if v@[i] != v@[(n - 1) - i] {
            count += 1;
        }
        i += 1;
    }

    assert(count == diff(zip_halves(v@))) by {
        // Prove that the manually constructed `diff` is equal to `diff(zip_halves(v@))`

        // First, prove that `diff(zip_halves(v@))` is equivalent to the sum
        // of 1s where elements are different.
        let zipped_seq = zip_halves(v@);
        assert(zipped_seq.len() == (v@.len() / 2) as int); // From zip_halves definition

        assert(diff(zipped_seq) ==
            Seq::new(zipped_seq.len() as nat, |k: nat| {
                if zipped_seq.index(k).0 != zipped_seq.index(k).1 { 1 } else { 0 }
            }).fold_left(0, |acc, x| acc + x)
        ) by {
            assert forall |k: int| 0 <= k < zipped_seq.len() implies #[trigger] zipped_seq.index(k) == (v.take(zipped_seq.len()).index(k), v.skip((v.len() + 1) / 2).reverse().index(k)) by {
                assert (v.take(zipped_seq.len()).index(k)).0 == v.take((v.len() / 2) as int).index(k) == v@[k];
                assert (v.skip(((v.len() + 1) / 2) as int).reverse().index(k)).1 == v.skip(((v.len() + 1) / 2) as int).reverse().index(k);
                let q = (v.len() + 1) / 2;
                let rlen = v.skip(q).len();
                let rev_idx = rlen as int - 1 - k;
                assert (v.skip(q).reverse()).index(k) == v.skip(q).index(rev_idx) == v@[q + rev_idx];
                assert q + rev_idx == q + (rlen - 1 - k) == (v.len() + 1) / 2 + (v.len() - (v.len() + 1) / 2) - 1 - k == v.len() - 1 - k;
            }
        };

        // Now, relate this to the loop's `count` calculation.
        // We need to show that `v@[k] != v@[(n - 1) - k]` is equivalent to the condition inside diff.
        // The `zip_halves` function pairs `v@[k]` with `v@[(n-1)-k]`.
        let len_half = (v@.len() / 2) as int;
        assert forall |k: nat| 0 <= k < len_half implies
            (zipped_seq.index(k).0 != zipped_seq.index(k).1) <==> (v@[k] != v@[(n - 1) - k])
        by {
            assert(zipped_seq.index(k).0 == v@[k]);
            let right_half_len = v@.len() - (v@.len() + 1) / 2;
            let skip_len = (v@.len() + 1) / 2;
            let reversed_idx = right_half_len as int - 1 - k;
            assert(v.skip((v.len() + 1) / 2).reverse().index(k) == v@[(skip_len + reversed_idx) as int]);
            assert((skip_len + reversed_idx) as int == (v@.len() + 1) / 2 + (v@.len() - (v@.len() + 1) / 2) - 1 - k as int == v@.len() - 1 - k as int);
        }

        let sum_from_zipped = Seq::new(zipped_seq.len() as nat, |k: nat| {
            if zipped_seq.index(k).0 != zipped_seq.index(k).1 { 1 } else { 0 }
        }).fold_left(0, |acc, x| acc + x);

        let sum_from_v = Seq::new(len_half as nat, |j: nat| {
            if v@[j] != v@[(n - 1) - j] { 1 } else { 0 }
        }).fold_left(0, |acc, x| acc + x);

        assert(sum_from_zipped == sum_from_v);
    };

    count
}
// </vc-code>

fn main() {}
}