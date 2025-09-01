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
// Added helper to prove diff(s) ≤ s.len()
proof fn diff_le_len(s: Seq<(i32, i32)>) 
    decreases s.len()
{
    reveal(diff);
    if s.len() == 0 {
        assert(diff(s) == 0);
    } else {
        let head = s@[0];
        let tail = s.skip(1);
        assert(diff(s) == (if head.0 != head.1 { 1 } else { 0 }) + diff(tail));
        diff_le_len(tail);
        assert(diff(tail) <= tail.len());
        assert((if head.0 != head.1 { 1 } else { 0 }) + diff(tail) <= 1 + tail.len());
        assert(1 + tail.len() == s.len());
    }
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
    // impl-start
    let n: usize = v@.len();
    let half: usize = n / 2;
    let mut i: usize = 0;
    let mut c: int = 0;
    while (i < half)
        invariant {
            i <= half;
            0 <= c;
            c == diff(zip_halves(v@).take(i as int));
        }
        decreases { (half as int) - (i as int) }
    {
        let idx: int = i as int;
        // We relate the i-th element of zip_halves(v@) with v@ indices.
        proof {
            reveal(zip_halves);
            // bounds for idx
            assert(idx >= 0);
            assert(idx < n as int);
            // First component comes from take(...)
            assert(v@.take((n / 2) as int)@[idx] == v@[idx]);
            // For the second component, work with skip(...) and reverse().
            let skip_k: int = ((n + 1) / 2) as int;
            let skipped: Seq<i32> = v@.skip(skip_k);
            assert(skipped.len() == (n as int) - skip_k);
            // reverse index: skipped.reverse()@[idx] == skipped@[skipped.len() - 1 - idx]
            assert(skipped.reverse()@[idx] == skipped@[skipped.len() - 1 - idx]);
            // skip index: skipped@[skipped.len() - 1 - idx] == v@ [ skip_k + (skipped.len() - 1 - idx) ]
            assert(skipped@[skipped.len() - 1 - idx] == v@[(skip_k + (skipped.len() - 1 - idx))]);
            // arithmetic: skip_k + (skipped.len() - 1 - idx) == n as int - 1 - idx
            assert(skip_k + (skipped.len() - 1 - idx) == (n as int) - 1 - idx);
            // thus second component equals v@[(n as int) - 1 - idx]
            // zip_with index: zip of take(...) and skipped.reverse()
            let left: Seq<i32> = v@.take((n / 2) as int);
            let right_rev: Seq<i32> = skipped.reverse();
            assert(left.zip_with(right_rev)@[idx].0 == left@[idx]);
            assert(left.zip_with(right_rev)@[idx].1 == right_rev@[idx]);
            assert(left@[idx] == v@[idx]);
            assert(right_rev@[idx] == v@[(n as int) - 1 - idx]);
        }
        // update count using direct comparison of v@ elements
        if v@[idx] != v@[((n as int) - 1) - idx] {
            c += 1;
        }
        i += 1;
    }
    proof {
        // From the loop invariant with i == half we get c == diff(zip_halves(v@).take(half as int))
        assert(c == diff(zip_halves(v@).take(half as int)));
        reveal(zip_halves);
        // zip_halves length equals half
        assert(zip_halves(v@).len() == (half as int));
        // taking full length yields the sequence itself
        assert(diff(zip_halves(v@).take(half as int)) == diff(zip_halves(v@)));
    }
    // c is non-negative and ≤ half, so casting to usize is safe
    assert(0 <= c);
    // Use lemma to bound diff by length
    diff_le_len(zip_halves(v@).take(half as int));
    assert(c <= (half as int));
    let change: usize = c as usize;
    change
    // impl-end
}
// </vc-code>

fn main() {}
}