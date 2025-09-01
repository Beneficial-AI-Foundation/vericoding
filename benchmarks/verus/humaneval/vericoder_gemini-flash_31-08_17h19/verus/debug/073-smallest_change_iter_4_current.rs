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
spec fn zip_halves_proof_lemma<T>(v: Seq<T>)
    ensures
        zip_halves(v).len() == (v.len() / 2) as nat,
        forall |k: int| 0 <= k < (v.len() / 2) as int ==>
            #[trigger] zip_halves(v).index(k).0 == v.index(k) &&
            #[trigger] zip_halves(v).index(k).1 == v.index((v.len() - 1 - k) as int),
{
    reveal(zip_halves);
    /* This lemma is used to prove properties about the `zip_halves` function. It states two main things:
     * 1. The length of the zipped sequence is `v.len() / 2`.
     * 2. For any index `k` within the bounds of the zipped sequence, the first element of the pair
     *    is `v.index(k)` and the second element is `v.index(v.len() - 1 - k)`.
     * These properties are crucial for relating the `diff` function's output to the `count` calculation.
     */
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
    let mut count: usize = 0;
    let n = v.len();
    let mid = n / 2;

    // The problem definition of `zip_halves` means that the middle element of an
    // odd-length input sequence is not paired and therefore does not contribute
    // to the `diff` calculation. Thus, no special handling is needed here.

    let mut i: usize = 0;
    while i < mid
        invariant
            0 <= i as int && i as int <= mid as int,
            count
                == Seq::new(i as nat, |j: int| {
                    if v@[j] != v@[(n as int - 1 - j)] {
                        1
                    } else {
                        0
                    }
                })
                .fold_left(0, |acc, x| acc + x),
    {
        if v@[i] != v@[(n as int - 1 - i)] {
            count += 1;
        }
        i += 1;
    }

    assert(count == diff(zip_halves(v@))) by {
        // By the end of the loop, count is equal to the sum of 1s where v[j] != v[n-1-j] for j from 0 to mid-1.
        // We need to show that this is equal to diff(zip_halves(v@)).

        // First, establish properties of zip_halves using the lemma
        zip_halves_proof_lemma(v@);
        let zipped_seq = zip_halves(v@);

        // We know from the lemma that zipped_seq.len() == v@.len() / 2.
        // And for 0 <= k < zipped_seq.len(), zipped_seq.index(k) == (v.index(k), v.index(v.len() - 1 - k)).

        // The definition of diff:
        // diff(s) = s.fold_left(0, |acc, x| if x.0 != x.1 { acc + 1 } else { acc })
        // This means diff(zipped_seq) is the count of pairs (x.0, x.1) in zipped_seq where x.0 != x.1.

        // We can express diff(zipped_seq) as a sum over its elements:
        assert(diff(zipped_seq) ==
            Seq::new(zipped_seq.len() as nat, |k: int| {
                if zipped_seq.index(k).0 != zipped_seq.index(k).1 { 1 } else { 0 }
            }).fold_left(0, |acc, x| acc + x)
        ) by {
            // This is direct from the definition of fold_left and diff.
        };

        // Now, substitute the values from zipped_seq using the lemma:
        assert forall |k: int| 0 <= k < zipped_seq.len() as int implies
            (zipped_seq.index(k).0 != zipped_seq.index(k).1) <==> (v@[k] != v@[(n as int - 1 - k) as int])
        by {
            zip_halves_proof_lemma(v@); // Re-establish lemma for the quantifier proof
        };

        // This allows us to equate the sum over zipped_seq and the sum inside the loop invariant:
        let sum_from_zipped = Seq::new(zipped_seq.len() as nat, |k: int| {
            if zipped_seq.index(k).0 != zipped_seq.index(k).1 { 1 } else { 0 }
        }).fold_left(0, |acc, x| acc + x);

        let sum_from_v = Seq::new(mid as nat, |j: int| {
            if v@[j] != v@[(n as int - 1 - j)] { 1 } else { 0 }
        }).fold_left(0, |acc, x| acc + x);

        assert(sum_from_zipped == sum_from_v) by {
             // Since zipped_seq.len() == mid, and their elements' conditions are equivalent.
        };

        // From the loop invariant, `count` equals `sum_from_v` at the end of the loop.
        // Therefore, `count` must be equal to `diff(zipped_seq)`.
    };

    count
}
// </vc-code>

fn main() {}
}