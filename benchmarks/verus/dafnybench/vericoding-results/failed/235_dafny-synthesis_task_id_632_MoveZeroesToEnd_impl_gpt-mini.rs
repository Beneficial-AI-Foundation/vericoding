use vstd::prelude::*;

verus! {

fn swap(arr: &mut Vec<i32>, i: usize, j: usize)
    requires 
        old(arr).len() > 0,
        i < old(arr).len(),
        j < old(arr).len(),
    ensures
        arr[i as int] == old(arr)[j as int],
        arr[j as int] == old(arr)[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> arr[k] == old(arr)[k],
        arr@.to_multiset() == old(arr)@.to_multiset(),
{
    assume(false);
}

spec fn count(arr: Seq<i32>, value: i32) -> nat
    decreases arr.len(),
{
    if arr.len() == 0 {
        0nat
    } else {
        (if arr[0] == value { 1nat } else { 0nat }) + count(arr.skip(1), value)
    }
}

proof fn count_bound(arr: Seq<i32>, value: i32)
    ensures count(arr, value) <= arr.len(),
    decreases arr.len(),
{
    if arr.len() == 0 {
    } else {
        count_bound(arr.skip(1), value);
    }
}

// <vc-helpers>
spec fn nz_count_prefix(arr: Seq<i32>, k: nat) -> nat
    requires k <= arr.len(),
    decreases k
{
    if k == 0 {
        0
    } else {
        let prev = nz_count_prefix(arr, k - 1);
        if arr[(k - 1) as int] != 0 {
            prev + 1
        } else {
            prev
        }
    }
}

spec fn nz_seq_prefix(arr: Seq<i32>, k: nat) -> Seq<i32>
    requires k <= arr.len(),
    decreases k
{
    if k == 0 {
        Seq::empty()
    } else {
        let prev = nz_seq_prefix(arr, k - 1);
        if arr[(k - 1) as int] != 0 {
            prev + Seq::from_ref(&[arr[(k - 1) as int]])
        } else {
            prev
        }
    }
}

proof fn nz_plus_zero_equals_len(arr: Seq<i32>)
    ensures nz_count_prefix(arr, arr.len()) + count(arr, 0) == arr.len(),
    decreases arr.len(),
{
    if arr.len() == 0 {
        // 0 + 0 == 0
    } else {
        let n = arr.len();
        // apply lemma to prefix of length n-1
        nz_plus_zero_equals_len(arr.take(n - 1));
        let last = arr[(n - 1) as int];
        if last == 0 {
            // nz_count_prefix(arr, n) == nz_count_prefix(prefix, n-1)
            // count(arr,0) == count(prefix,0) + 1
            // so sum equals n
            assert(nz_count_prefix(arr, n) == nz_count_prefix(arr.take(n - 1), n - 1));
            assert(count(arr, 0) == count(arr.take(n - 1), 0) + 1);
            assert(nz_count_prefix(arr.take(n - 1), n - 1) + count(arr.take(n - 1), 0) + 1 == n);
        } else {
            // nz_count_prefix(arr, n) == nz_count_prefix(prefix, n-1) + 1
            // count(arr,0) == count(prefix,0)
            assert(nz_count_prefix(arr, n) == nz_count_prefix(arr.take(n - 1), n - 1) + 1);
            assert(count(arr, 0) == count(arr.take(n - 1), 0));
            assert(nz_count_prefix(arr.take(n - 1), n - 1) + 1 + count(arr.take(n - 1), 0) == n);
        }
    }
}

proof fn nz_seq_prefix_index(arr: Seq<i32>, k: nat, i: nat)
    requires k <= arr.len(),
    requires i < k,
    requires arr[(i) as int] != 0,
    ensures nz_seq_prefix(arr, k)@[ (nz_count_prefix(arr, i + 1) - 1) as int ] == arr[(i) as int],
    decreases k
{
    // From i < k we get k > 0
    assert(k > 0);
    if k == 1 {
        // then i == 0
        assert(i == 0);
        // nz_count_prefix(arr,1) == 1 and nz_seq_prefix(arr,1) == [arr[0]] because arr[0] != 0
        assert(nz_count_prefix(arr, 1) == (if arr[(0) as int] != 0 { 1 } else { 0 }));
        assert(nz_seq_prefix(arr, 1) == (if arr[(0) as int] != 0 { Seq::from_ref(&[arr[(0) as int]]) } else { Seq::empty() }));
        assert(nz_count_prefix(arr, 1) == 1);
        assert(nz_seq_prefix(arr, 1)@[0] == arr[(0) as int]);
        assert(nz_seq_prefix(arr, 1)@[ (nz_count_prefix(arr, 1) - 1) as int ] == arr[(0) as int]);
    } else {
        // k >= 2
        if k - 1 == i {
            // last element is the one
            if arr[(k - 1) as int] != 0 {
                assert(nz_count_prefix(arr, k) == nz_count_prefix(arr, k - 1) + 1);
                assert(nz_seq_prefix(arr, k) == nz_seq_prefix(arr, k - 1) + Seq::from_ref(&[arr[(k - 1) as int]]));
                assert(nz_seq_prefix(arr, k)@[ (nz_count_prefix(arr, k) - 1) as int ] == arr[(k - 1) as int]);
                assert(nz_count_prefix(arr, i + 1) == nz_count_prefix(arr, k));
                assert(nz_seq_prefix(arr, k)@[ (nz_count_prefix(arr, i + 1) - 1) as int ] == arr[(i) as int]);
            } else {
                // contradicts requires arr[i] != 0
                assert(false);
            }
        } else {
            // i < k-1, apply induction on k-1
            nz_seq_prefix_index(arr, k - 1, i);
            if arr[(k - 1) as int] != 0 {
                assert(nz_seq_prefix(arr, k) == nz_seq_prefix(arr, k - 1) + Seq::from_ref(&[arr[(k - 1) as int]]));
                assert(nz_count_prefix(arr, k) == nz_count_prefix(arr, k - 1) + 1);
            } else {
                assert(nz_seq_prefix(arr, k) == nz_seq_prefix(arr, k - 1));
                assert(nz_count_prefix(arr, k) == nz_count_prefix(arr, k - 1));
            }
            assert(nz_seq_prefix(arr, k)@[ (nz_count_prefix(arr, i + 1) - 1) as int ] ==
                   nz_seq_prefix(arr, k - 1)@[ (nz_count_prefix(arr, i + 1) - 1) as int ]);
            assert(nz_seq_prefix(arr, k)@[ (nz_count_prefix(arr, i + 1) - 1) as int ] == arr[(i) as int]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn move_zeros_to_end(arr: &mut Vec<i32>)
    requires old(arr).len() >= 2,
    ensures
        // Same size
        arr.len() == old(arr).len(),
        // Zeros to the right of the first zero
        forall|i: int, j: int| 0 <= i < j < arr.len() && arr[i] == 0 ==> arr[j] == 0,
        // The final array is a permutation of the original one
        arr@.to_multiset() == old(arr)@.to_multiset(),
        // Relative order of non-zero elements is preserved
        forall|n: int, m: int| 0 <= n < m < arr.len() && old(arr)[n] != 0 && old(arr)[m] != 0 ==>
            exists|k: int, l: int| 0 <= k < l < arr.len() && arr[k] == old(arr)[n] && arr[l] == old(arr)[m],
        // Number of zeros is preserved
// </vc-spec>
// <vc-code>
{
    // Snapshot the original vector
    let orig = arr.clone();

    // Clear the target vector and rebuild: non-zeros in order, then zeros
    arr.clear();
    let mut zeros: usize = 0;
    let mut idx: usize = 0;
    while idx < orig.len() {
        invariant idx <= orig.len();
        invariant arr.len() as nat == nz_count_prefix(orig@, idx as nat);
        invariant arr@ == nz_seq_prefix(orig@, idx as nat);
        invariant zeros + arr.len() == idx;
        if orig[idx] != 0 {
            arr.push(orig[idx]);
        } else {
            zeros = zeros + 1;
        }
        idx = idx + 1;
    }

    let mut z: usize = 0;
    while z < zeros {
        invariant z <= zeros;
        invariant arr.take(nz_count_prefix(orig@, orig.len() as nat)) == nz_seq_prefix(orig@, orig.len() as nat);
        invariant arr.len() as nat == nz_count_prefix(orig@, orig.len() as nat) + (z as nat);
        arr.push(0);
        z = z + 1;
    }

    proof {
        // Length preserved (as nats)
        assert((arr.len() as nat) == nz_count_prefix(orig@, orig.len() as nat) + (zeros as nat));
        nz_plus_zero_equals_len(orig@);
        assert((zeros as nat) == count(orig@, 0));
        assert((arr.len() as nat) == orig.len() as nat);
        assert(arr.len() == orig.len());

        // Multiset preserved: counts for each value are equal
        forall|v: i32| {
            if v == 0 {
                assert(count(arr@, v) == count(orig@, v));
            } else {
                // Non-zero values only appear in the prefix part of arr which equals nz_seq_prefix(orig)
                // and nz_seq_prefix preserves order and elements of non-zero values from orig.
                assert(count(arr@, v) == count(orig@, v));
            }
        }
        assert(arr@.to_multiset() == orig@.to_multiset());

        // Relative order of non-zero elements is preserved
        forall|n: int, m: int| (requires 0 <= n && n < m && m < orig.len() as int && orig@[n] != 0 && orig@[m] != 0) {
            let kn = (nz_count_prefix(orig@, (n as nat) + 1) - 1) as int;
            let km = (nz_count_prefix(orig@, (m as nat) + 1) - 1) as int;
            assert(kn < km);

            nz_seq_prefix_index(orig@, orig.len() as nat, (n as nat));
            nz_seq_prefix_index(orig@, orig.len() as nat, (m as nat));

            assert(arr.take(nz_count_prefix(orig@, orig.len() as nat))@[kn] == orig@[n]);
            assert(arr.take(nz_count_prefix(orig@, orig.len() as nat))@[km] == orig@[m]);

            assert(0 <= kn && kn < arr.len() as int);
            assert(0 <= km && km < arr.len() as int);
            assert(kn < km);

            exists|k: int, l: int| 0 <= k && k < l && l < arr.len() as int &&
                arr@[k] == orig@[n] && arr@[l] == orig@[m];
        }
    }
}
// </vc-code>

fn main() {}

}