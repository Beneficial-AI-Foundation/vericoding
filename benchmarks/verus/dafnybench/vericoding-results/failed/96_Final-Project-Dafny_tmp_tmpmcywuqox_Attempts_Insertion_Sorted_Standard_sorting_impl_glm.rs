use vstd::prelude::*;

verus! {

spec fn insertion_sorted(array: Seq<int>, left: int, right: int) -> bool
    recommends 0 <= left <= right <= array.len()
{
    forall|i: int, j: int| left <= i < j < right ==> array[i] <= array[j]
}

// <vc-helpers>
proof fn lemma_insertion_sorted_middle(array: Seq<int>, left: int, right: int)
    requires 0 <= left <= right <= array.len()
    requires insertion_sorted(array, left, right)
    ensures insertion_sorted(array, left + 1, right)
{
    assert forall|i: int, j: int| left + 1 <= i < j < right implies #[trigger] array[i] <= array[j] by {
        assert(left <= i < j < right);
    }
}

proof fn lemma_insertion_sorted_append(array: Seq<int>, left: int, right: int)
    requires 0 <= left <= right <= array.len()
    requires insertion_sorted(array, left, right)
    requires right < array.len()
    requires forall|i: int| left <= i < right ==> #[trigger] array[i] <= array[right]
    ensures insertion_sorted(array, left, right + 1)
{
    assert forall|i: int, j: int| left <= i < j < right + 1 implies #[trigger] array[i] <= array[j] by {
        if j < right {
            assert(left <= i < j < right);
        } else {
            assert(j == right);
            assert(left <= i < right);
        }
    }
}

proof fn lemma_insertion_sorted_shift(array: Seq<int>, left: int, right: int, k: int, x: int)
    requires 0 <= left <= k + 1 <= right + 1 <= array.len()
    requires insertion_sorted(array, left, right)
    requires forall|i: int| k + 1 <= i < right + 1 ==> array[i] == old(array)[i - 1]
    requires forall|i: int| left <= i <= k ==> array[i] == old(array)[i]
    requires forall|i: int| k < i < right + 1 ==> old(array)[i - 1] >= x
    requires array[k + 1] == x
    requires forall|i: int| left <= i <= k ==> old(array)[i] <= x
    ensures insertion_sorted(array, left, right + 1)
{
    assert forall|i: int, j: int| left <= i < j < right + 1 implies #[trigger] array[i] <= array[j] by {
        if j < right + 1 && j != k + 1 {
            if j <= k {
                assert(left <= i < j <= k);
                assert(old(array)[i] <= old(array)[j]);
                assert(array[i] == old(array)[i]);
                assert(array[j] == old(array)[j]);
            } else {
                assert(j > k);
                if i <= k {
                    assert(old(array)[i] <= x);
                    assert(x <= array[j]);
                    assert(array[i] == old(array)[i]);
                } else {
                    assert(i > k);
                    assert(old(array)[i - 1] <= old(array)[j - 1]);
                    assert(array[i] == old(array)[i - 1]);
                    assert(array[j] == old(array)[j - 1]);
                }
            }
        } else if j == k + 1 {
            assert(array[i] <= x);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sorting(array: &mut Vec<int>)
    requires old(array).len() > 1
    ensures insertion_sorted(array@, 0, array@.len() as int)
// </vc-spec>
// <vc-code>
{
    let n = array.len();
    let mut i = 1;
    while i < n
        invariant 0 < i <= n
        invariant insertion_sorted(array@, 0, i as int)
    {
        let j = i;
        let x = array[i];
        let mut k: isize = (i - 1) as isize;
        while k >= 0 && array[k as usize] > x
            invariant -1 <= k < i as isize
            invariant forall|m: int| k as int < m < i as int implies #[trigger] array@[m as usize] >= x
            invariant insertion_sorted(array@, 0, i as int)
        {
            array[(k + 1) as usize] = array[k as usize];
            k = k - 1;
        }
        array[(k + 1) as usize] = x;
        
        proof {
            lemma_insertion_sorted_append(array@, 0, i as int);
            assert forall|m: int| 0 <= m < i as int implies #[trigger] old(array)@[m] <= array@[i] by {
                if m <= k as int {
                    assert(insertion_sorted(array@, 0, i as int));
                    assert(old(array)@[m] == array@[m as usize]);
                    assert(array@[m as usize] <= array@[k as usize]);
                    assert(array@[k as usize] <= x);
                    assert(x == array@[i]);
                } else {
                    assert(old(array)@[m] == array@[m as usize]);
                    assert(array@[m as usize] >= x);
                    assert(x == array@[i]);
                }
            }
            lemma_insertion_sorted_shift(array@, 0, i as int, k as int, x);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}