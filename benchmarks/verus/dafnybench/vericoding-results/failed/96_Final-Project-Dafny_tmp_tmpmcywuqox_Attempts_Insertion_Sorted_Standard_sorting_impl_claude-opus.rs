use vstd::prelude::*;

verus! {

spec fn insertion_sorted(array: Seq<int>, left: int, right: int) -> bool
    recommends 0 <= left <= right <= array.len()
{
    forall|i: int, j: int| left <= i < j < right ==> array[i] <= array[j]
}

// <vc-helpers>
proof fn sorted_extend(array: Seq<int>, left: int, right: int, val: int)
    requires
        0 <= left <= right < array.len(),
        insertion_sorted(array, left, right),
        right > left,
        array[right - 1] <= val,
    ensures
        insertion_sorted(array.update(right, val), left, right + 1)
{
    assert forall|i: int, j: int| left <= i < j < right + 1 implies #[trigger] array.update(right, val)[i] <= #[trigger] array.update(right, val)[j] by {
        if j == right {
            if i < right - 1 {
                assert(array[i] <= array[right - 1]);
                assert(array[right - 1] <= val);
            }
        } else {
            assert(array[i] <= array[j]);
        }
    }
}

proof fn sorted_swap_adjacent(array: Seq<int>, left: int, right: int, k: int)
    requires
        0 <= left <= k < k + 1 < right <= array.len(),
        insertion_sorted(array, left, right),
        array[k] > array[k + 1],
    ensures
        insertion_sorted(array.update(k, array[k + 1]).update(k + 1, array[k]), left, right)
{
    let swapped = array.update(k, array[k + 1]).update(k + 1, array[k]);
    assert forall|i: int, j: int| left <= i < j < right implies #[trigger] swapped[i] <= #[trigger] swapped[j] by {
        if i == k && j == k + 1 {
            assert(swapped[i] == array[k + 1]);
            assert(swapped[j] == array[k]);
            assert(array[k + 1] < array[k]);
        } else if i == k {
            assert(j > k + 1);
            assert(swapped[i] == array[k + 1]);
            assert(swapped[j] == array[j]);
            assert(array[k + 1] <= array[k]);
            assert(array[k] <= array[j]);
        } else if j == k + 1 {
            assert(i < k);
            assert(swapped[i] == array[i]);
            assert(swapped[j] == array[k]);
            assert(array[i] <= array[k]);
        } else if i == k + 1 {
            assert(j > k + 1);
            assert(swapped[i] == array[k]);
            assert(swapped[j] == array[j]);
            assert(array[k] <= array[j]);
        } else {
            assert(swapped[i] == array[i]);
            assert(swapped[j] == array[j]);
            assert(array[i] <= array[j]);
        }
    }
}

proof fn sorted_merge(array: Seq<int>, left: int, mid: int, right: int)
    requires
        0 <= left <= mid <= right <= array.len(),
        insertion_sorted(array, left, mid),
        insertion_sorted(array, mid, right),
        mid > left ==> mid < right ==> array[mid - 1] <= array[mid],
    ensures
        insertion_sorted(array, left, right)
{
    assert forall|i: int, j: int| left <= i < j < right implies #[trigger] array[i] <= #[trigger] array[j] by {
        if i < mid && j < mid {
            assert(insertion_sorted(array, left, mid));
        } else if i >= mid && j >= mid {
            assert(insertion_sorted(array, mid, right));
        } else {
            assert(i < mid && j >= mid);
            assert(array[i] <= array[mid - 1]);
            assert(array[mid - 1] <= array[mid]);
            assert(array[mid] <= array[j]);
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
    
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n,
            array.len() == n,
            insertion_sorted(array@, 0, i as int),
        decreases n - i
    {
        let mut j: usize = i;
        while j > 0 && array[j - 1] > array[j]
            invariant
                0 <= j <= i < n,
                array.len() == n,
                insertion_sorted(array@, 0, j as int),
                j < i ==> insertion_sorted(array@, (j + 1) as int, (i + 1) as int),
                j < i ==> array@[j as int] <= array@[(j + 1) as int],
                forall|k: int| j as int < k && k < i + 1 ==> array@[j as int] <= array@[k],
            decreases j
        {
            let val_j_minus_1 = array[j - 1];
            let val_j = array[j];
            
            array.set(j, val_j_minus_1);
            array.set(j - 1, val_j);
            
            proof {
                assert(0 <= 0 <= (j - 1) as int < j as int < (i + 1) as int <= n as int);
                sorted_swap_adjacent(old(array)@, 0, (i + 1) as int, (j - 1) as int);
                assert(insertion_sorted(array@, 0, (j - 1) as int));
                
                if j < i {
                    assert forall|k: int| (j - 1) as int < k && k < i + 1 implies array@[(j - 1) as int] <= array@[k] by {
                        if k == j as int {
                            assert(array@[(j - 1) as int] == old(array)@[j as int]);
                            assert(array@[j as int] == old(array)@[(j - 1) as int]);
                            assert(old(array)@[(j - 1) as int] > old(array)@[j as int]);
                            assert(array@[(j - 1) as int] <= array@[j as int]);
                        } else {
                            assert(old(array)@[j as int] <= old(array)@[k]);
                            assert(array@[(j - 1) as int] == old(array)@[j as int]);
                            assert(array@[k] == old(array)@[k]);
                        }
                    }
                }
            }
            
            j = j - 1;
        }
        
        proof {
            sorted_merge(array@, 0, (j + 1) as int, (i + 1) as int);
        }
        
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}