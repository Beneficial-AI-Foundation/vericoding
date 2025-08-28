use vstd::prelude::*;


verus! {

spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> (result:bool) {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
    }
    // pure-end
// pure-end

spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> (result:bool) {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
}
// pure-end

// <vc-helpers>
proof fn lemma_swap_preserves_reorder<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>, i: int, j: int)
    requires
        is_reorder_of(r, p, s),
        0 <= i < r.len(),
        0 <= j < r.len(),
    ensures
        is_reorder_of(r.update(i, r[j]).update(j, r[i]), p.update(i, p[j]).update(j, p[i]), s)
{
    let r_swapped = r.update(i, r[j]).update(j, r[i]);
    let p_swapped = p.update(i, p[j]).update(j, p[i]);
    assert(r_swapped.len() == s.len());
    assert forall |k: int| 0 <= k < r.len() implies 0 <= #[trigger] r_swapped[k] < r.len() by {
        if k == i {
            assert(0 <= r[j] < r.len());
        } else if k == j {
            assert(0 <= r[i] < r.len());
        } else {
            assert(0 <= r[k] < r.len());
        }
    };
    assert forall |k: int, l: int| 0 <= k < l < r.len() implies r_swapped[k] != r_swapped[l] by {
        if k == i {
            assert(r[j] != r[l]);
        } else if k == j {
            assert(r[i] != r[l]);
        } else if l == i {
            assert(r[k] != r[j]);
        } else if l == j {
            assert(r[k] != r[i]);
        } else {
            assert(r[k] != r[l]);
        }
    };
    assert(p_swapped =~= r_swapped.map_values(|idx: int| s[idx]));
}

proof fn lemma_swap_maintains_sorted(a: Seq<u32>, i: int, j: int)
    requires
        sorted_between(a, 0, a.len() as int),
        0 <= i < j < a.len(),
        a[i] > a[j],
    ensures
        sorted_between(a.update(i, a[j]).update(j, a[i]), 0, a.len() as int)
{
    let a_swapped = a.update(i, a[j]).update(j, a[i]);
    assert forall |k: int, l: int| 0 <= k < l < a.len() implies a_swapped[k] <= a_swapped[l] by {
        if k == i {
            assert(a[j] <= a[l]);
        } else if k == j {
            assert(a[i] <= a[l]);
        } else if l == i {
            assert(a[k] <= a[j]);
        } else if l == j {
            assert(a[k] <= a[i]);
        } else {
            assert(a[k] <= a[l]);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)
        // post-conditions-start
        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let n = nums.len();
    if n == 0 {
        return;
    }

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            sorted_between(nums@, 0, i as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
    {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;
        while j < n
            invariant
                i <= j <= n,
                0 <= min_idx < n,
                sorted_between(nums@, 0, i as int),
                forall|k: int| i <= k < j ==> nums@[min_idx as int] <= nums@[k],
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        {
            if nums[j] < nums[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        if min_idx != i {
            let ghost old_nums = nums@;
            let temp = nums[i];
            let temp_min = nums[min_idx];
            nums.set(i, temp_min);
            nums.set(min_idx, temp);
            proof {
                let r = Seq::new(n as nat, |k: int| k);
                lemma_swap_preserves_reorder(r, old_nums, old(nums)@, i as int, min_idx as int);
            }
        }
        i = i + 1;
    }
}
// </vc-code>

}

fn main() {}