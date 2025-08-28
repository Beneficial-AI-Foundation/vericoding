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
proof fn sorted_range_merge(v: Seq<u32>, start: int, mid: int, end: int)
    requires
        0 <= start <= mid <= end <= v.len(),
        sorted_between(v, start, mid),
        sorted_between(v, mid, end),
        mid == start || mid == end || v[mid - 1] <= v[mid]
    ensures
        sorted_between(v, start, end)
{
    assert forall |i: int, j: int| start <= i < j < end implies v[i] <= v[j] by {
        if i < mid && j < mid {
            assert(v[i] <= v[j]);
        } else if i >= mid && j >= mid {
            assert(v[i] <= v[j]);
        } else if i < mid && j >= mid {
            if mid > start && mid < end {
                assert(v[i] <= v[mid - 1] <= v[mid] <= v[j]);
            }
        }
    }
}

proof fn merge_preserves_reorder(
    left: Seq<u32>, right: Seq<u32>, merged: Seq<u32>,
    left_reorder: Seq<int>, right_reorder: Seq<int>,
    orig_left: Seq<u32>, orig_right: Seq<u32>
)
    requires
        is_reorder_of(left_reorder, left, orig_left),
        is_reorder_of(right_reorder, right, orig_right),
        merged == merge_sequences(left, right)
    ensures
        exists|r: Seq<int>| is_reorder_of(r, merged, orig_left + orig_right)
{
}

spec fn merge_sequences(left: Seq<u32>, right: Seq<u32>) -> Seq<u32>
    decreases left.len() + right.len()
{
    if left.len() == 0 {
        right
    } else if right.len() == 0 {
        left
    } else if left[0] <= right[0] {
        seq![left[0]] + merge_sequences(left.drop_first(), right)
    } else {
        seq![right[0]] + merge_sequences(left, right.drop_first())
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
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
    let len = nums.len();
    if len <= 1 {
        proof {
            assert(sorted_between(nums@, 0, nums@.len() as int));
            let identity_reorder = Seq::new(nums@.len(), |i| i);
            assert(is_reorder_of(identity_reorder, nums@, old(nums)@));
        }
        return;
    }
    
    let mut size = 1;
    while size < len
        invariant
            size >= 1,
            size <= len,
            forall|start: int| 0 <= start < nums@.len() && start + size <= nums@.len() 
                ==> sorted_between(nums@, start, min(start + size, nums@.len() as int)),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)
        decreases len - size
    {
        let mut start = 0;
        while start < len
            invariant
                start <= len,
                size >= 1,
                size < len,
                forall|s: int| 0 <= s < start && s + 2 * size <= nums@.len()
                    ==> sorted_between(#[trigger] nums@, s, min(s + 2 * size, nums@.len() as int)),
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)
            decreases len - start
        {
            let mid = if start + size <= len { start + size } else { len };
            let end = if start + 2 * size <= len { start + 2 * size } else { len };
            
            if mid < end {
                merge_in_place(nums, start, mid, end);
            }
            
            start += 2 * size;
        }
        size *= 2;
    }
}

fn merge_in_place(nums: &mut Vec<u32>, start: usize, mid: usize, end: usize)
    requires
        start <= mid <= end <= old(nums).len(),
        sorted_between(old(nums)@, start as int, mid as int),
        sorted_between(old(nums)@, mid as int, end as int)
    ensures
        nums.len() == old(nums).len(),
        sorted_between(nums@, start as int, end as int),
        exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)
{
    let mut temp = Vec::new();
    let mut i = start;
    let mut j = mid;
    
    while i < mid && j < end
        invariant
            start <= i <= mid,
            mid <= j <= end,
            temp.len() == (i - start) + (j - mid),
            sorted_between(temp@, 0, temp@.len() as int)
        decreases (mid - i) + (end - j)
    {
        if nums[i] <= nums[j] {
            temp.push(nums[i]);
            i += 1;
        } else {
            temp.push(nums[j]);
            j += 1;
        }
    }
    
    while i < mid
        invariant
            start <= i <= mid,
            j == end,
            temp.len() == (i - start) + (end - mid),
            sorted_between(temp@, 0, temp@.len() as int)
        decreases mid - i
    {
        temp.push(nums[i]);
        i += 1;
    }
    
    while j < end
        invariant
            i == mid,
            mid <= j <= end,
            temp.len() == (mid - start) + (j - mid),
            sorted_between(temp@, 0, temp@.len() as int)
        decreases end - j
    {
        temp.push(nums[j]);
        j += 1;
    }
    
    for k in 0..temp.len()
        invariant
            temp.len() == end - start,
            sorted_between(temp@, 0, temp@.len() as int),
            forall|idx: int| 0 <= idx < k ==> nums@[start + idx] == temp@[idx]
    {
        nums.set(start + k, temp[k]);
    }
}
// </vc-code>

}

fn main() {}