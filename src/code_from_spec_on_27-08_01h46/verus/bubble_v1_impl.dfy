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
proof fn sorted_between_empty(a: Seq<u32>, from: int, to: int)
    requires from >= to
    ensures sorted_between(a, from, to)
{
}

proof fn sorted_between_single(a: Seq<u32>, from: int, to: int)
    requires from + 1 >= to
    ensures sorted_between(a, from, to)
{
}

proof fn sorted_between_extends(a: Seq<u32>, from: int, to: int, x: u32)
    requires 
        sorted_between(a, from, to),
        to >= 0,
        forall|i: int| from <= i < to ==> a[i] <= x
    ensures sorted_between(a.push(x), from, to + 1)
{
}

spec fn identity_reorder(n: int) -> Seq<int>
    decreases n
{
    if n <= 0 {
        seq![]
    } else {
        identity_reorder(n - 1).push(n - 1)
    }
}

proof fn identity_reorder_properties<T>(s: Seq<T>)
    ensures 
        identity_reorder(s.len() as int).len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] identity_reorder(s.len() as int)[i] < s.len(),
        forall|i: int, j: int| 0 <= i < j < s.len() ==> identity_reorder(s.len() as int)[i] != identity_reorder(s.len() as int)[j],
        s =~= identity_reorder(s.len() as int).map_values(|idx: int| s[idx])
{
    let r = identity_reorder(s.len() as int);
    
    assert forall|i: int| 0 <= i < s.len() implies 0 <= #[trigger] r[i] < s.len() by {
        assert(r[i] == i);
    }
    
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies r[i] != r[j] by {
        assert(r[i] == i && r[j] == j);
    }
    
    assert forall|i: int| 0 <= i < s.len() implies s[i] == (r.map_values(|idx: int| s[idx]))[i] by {
        assert(r.map_values(|idx: int| s[idx])[i] == s[r[i]]);
        assert(r[i] == i);
    }
}

proof fn is_reorder_of_identity<T>(s: Seq<T>)
    ensures is_reorder_of(identity_reorder(s.len() as int), s, s)
{
    identity_reorder_properties(s);
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
    
    for i in 0..len
        invariant
            sorted_between(nums@, 0, i as int),
            nums@.len() == len,
    {
        let mut min_idx = i;
        for j in (i + 1)..len
            invariant
                i <= min_idx < len,
                nums@.len() == len,
                sorted_between(nums@, 0, i as int),
                forall|k: int| i <= k < j ==> nums@[min_idx as int] <= nums@[k],
        {
            if nums[j] < nums[min_idx] {
                min_idx = j;
            }
        }
        
        if min_idx != i {
            let temp = nums[i];
            let min_val = nums[min_idx];
            nums.set(i, min_val);
            nums.set(min_idx, temp);
        }
    }
    
    proof {
        assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)) by {
            identity_reorder_properties(old(nums)@);
            assert(is_reorder_of(identity_reorder(old(nums)@.len() as int), old(nums)@, old(nums)@));
        }
    }
}
// </vc-code>

}

fn main() {}