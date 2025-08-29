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
proof fn identity_reorder<T>(s: Seq<T>)
    ensures exists|r: Seq<int>| is_reorder_of(r, s, s)
{
    let r = Seq::new(s.len(), |i: int| i);
    assert(r.len() == s.len());
    assert(forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()) by {
        assert(forall|i: int| 0 <= i < r.len() ==> r[i] == i);
    }
    assert(forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]) by {
        assert(forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] == i && r[j] == j);
    }
    assert(s =~= r.map_values(|i: int| s[i])) by {
        assert(forall|i: int| 0 <= i < s.len() ==> s[i] == r.map_values(|k: int| s[k])[i]);
    }
    assert(is_reorder_of(r, s, s));
}

proof fn base_case_invariants(nums: Seq<u32>, original: Seq<u32>)
    requires nums == original, nums.len() >= 1
    ensures 
        sorted_between(nums, 0, 1),
        exists|r: Seq<int>| is_reorder_of(r, nums, original)
{
    assert(sorted_between(nums, 0, 1)) by {
        assert(forall|i: int, j: int| 0 <= i < j < 1 ==> nums[i] <= nums[j]);
    }
    identity_reorder(nums);
}

fn insertion_sort(nums: &mut Vec<u32>)
    ensures
        sorted_between(nums@, 0, nums@.len() as int),
        exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
{
    let ghost original = nums@;
    let n = nums.len();
    
    if n <= 1 {
        proof {
            if n == 0 {
                assert(sorted_between(nums@, 0, 0));
                identity_reorder(nums@);
            } else {
                assert(sorted_between(nums@, 0, 1));
                identity_reorder(nums@);
            }
        }
        return;
    }
    
    proof {
        base_case_invariants(nums@, original);
    }
    
    for i in 1..n
        invariant
            nums@.len() == original.len(),
            nums@.len() == n,
            sorted_between(nums@, 0, i as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, original),
    {
        assert(i < nums.len());
        let key = nums[i];
        let mut j = i;
        
        proof {
            assert(j <= i);
            assert(sorted_between(nums@, 0, j as int));
            assert(sorted_between(nums@, (j as int) + 1, (i as int) + 2));
            assert(forall|k: int| (j as int) + 1 <= k <= (i as int) + 1 ==> nums@[k] > key) by {
                assert(forall|k: int| (j as int) + 1 <= k <= (i as int) + 1 ==> k == (i as int) + 1);
                assert((i as int) + 1 < nums@.len());
                assert(nums@[(i as int) + 1] == key);
            }
            assert(j == 0 || nums@[j - 1] <= key) by {
                if j > 0 {
                    assert(j - 1 == (i - 1) as int);
                    assert(sorted_between(nums@, 0, i as int));
                    assert((i - 1) as int < i as int);
                    assert(i as int < nums@.len());
                }
            }
        }
        
        while j > 0 && {
            assert(j >= 1);
            assert(j - 1 < nums.len());
            nums[j - 1] > key
        }
            invariant
                nums@.len() == original.len(),
                nums@.len() == n,
                j <= i,
                i < n,
                sorted_between(nums@, 0, (j as int)),
                sorted_between(nums@, (j as int) + 1, (i as int) + 2),
                forall|k: int| (j as int) + 1 <= k <= (i as int) + 1 ==> nums@[k] > key,
                j == 0 || nums@[j - 1] <= key,
                exists|r: Seq<int>| is_reorder_of(r, nums@, original),
            decreases j
        {
            let prev_val = nums[j - 1];
            nums.set(j, prev_val);
            j -= 1;
        }
        
        nums.set(j, key);
    }
}

proof fn empty_seq_sorted(s: Seq<u32>)
    requires s.len() == 0
    ensures sorted_between(s, 0, 0)
{}

proof fn single_element_sorted(s: Seq<u32>)
    requires s.len() == 1
    ensures sorted_between(s, 0, 1)
{}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    if nums.len() <= 1 {
        proof {
            if nums.len() == 0 {
                empty_seq_sorted(nums@);
                identity_reorder(nums@);
            } else {
                single_element_sorted(nums@);
                identity_reorder(nums@);
            }
        }
        return;
    }
    
    insertion_sort(nums);
}
// </vc-code>

}

fn main() {}