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
proof fn sorted_between_transitive(a: Seq<u32>, from: int, mid: int, to: int)
    requires
        from <= mid <= to,
        sorted_between(a, from, mid),
        sorted_between(a, mid, to),
        forall |i: int, j: int| from <= i < mid && mid <= j < to ==> a[i] <= a[j]
    ensures
        sorted_between(a, from, to)
{}

proof fn swap_preserves_reorder(v_old: Seq<u32>, v_new: Seq<u32>, r_old: Seq<int>, i: usize, j: usize)
    requires
        0 <= i < v_old.len(),
        0 <= j < v_old.len(),
        v_old.len() == v_new.len(),
        is_reorder_of(r_old, v_old, v_old),
        v_new == v_old.update(i as int, v_old[j as int]).update(j as int, v_old[i as int])
    ensures
        exists |r_new: Seq<int>| is_reorder_of(r_new, v_new, v_old)
{}

proof fn identity_is_reorder<T>(s: Seq<T>)
    ensures exists |r: Seq<int>| is_reorder_of(r, s, s)
{
    let r = Seq::new(s.len(), |i: int| i);
    assert(is_reorder_of(r, s, s));
}

fn vec_swap(v: &mut Vec<u32>, i: usize, j: usize)
    requires 
        i < old(v).len(),
        j < old(v).len()
    ensures
        v.len() == old(v).len(),
        v@[i as int] == old(v)@[j as int],
        v@[j as int] == old(v)@[i as int],
        forall |k: int| 0 <= k < v.len() && k != i && k != j ==> v@[k] == old(v)@[k]
{
    let temp = v[i];
    v.set(i, v[j]);
    v.set(j, temp);
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
    let ghost old_nums_at_start = nums@;
    
    proof {
        identity_is_reorder(nums@);
    }
    
    for i in 0..n
        invariant
            sorted_between(nums@, 0, i as int),
            exists |r: Seq<int>| is_reorder_of(r, nums@, old_nums_at_start)
    {
        let mut min_idx = i;
        for j in (i + 1)..n
            invariant
                i <= min_idx < n,
                forall |k: int| i <= k <= j ==> nums@[min_idx as int] <= nums@[k],
                exists |r: Seq<int>| is_reorder_of(r, nums@, old_nums_at_start)
        {
            if nums[j] < nums[min_idx] {
                min_idx = j;
            }
        }
        
        if min_idx != i {
            let ghost old_nums = nums@;
            vec_swap(nums, i, min_idx);
            proof {
                swap_preserves_reorder(old_nums, nums@, Seq::new(old_nums.len(), |k: int| k), i, min_idx);
            }
        }
    }
}
// </vc-code>

}

fn main() {}