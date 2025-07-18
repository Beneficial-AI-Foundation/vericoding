use vstd::prelude::*;
fn main() {}

verus! {
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> bool {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
    }
 
 
    spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
    }

    //IMPL test1
    fn test1(nums: &mut Vec<u32>)
        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
    {
        let len = nums.len();
        /* code modified by LLM (iteration 1): added proof that initial state satisfies invariants */
        assert(sorted_between(nums@, 0, 1));
        assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)) by {
            let identity_reorder = Seq::new(nums@.len() as nat, |i: int| i);
            assert(is_reorder_of(identity_reorder, nums@, old(nums)@));
        }
        
        for i in 1..len
            invariant
                sorted_between(nums@, 0, i as int),
                nums@.len() == old(nums)@.len(),
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        {
            let mut j = i;
            /* code modified by LLM (iteration 1): added bounds checking and fixed loop invariants */
            while j > 0 && j < nums.len() && (j - 1) < nums.len() && nums[j - 1] > nums[j]
                invariant
                    j <= i,
                    i < nums@.len(),
                    nums@.len() == old(nums)@.len(),
                    sorted_between(nums@, 0, j as int),
                    sorted_between(nums@, j as int, (i + 1) as int),
                    j < i && j < nums@.len() && (j + 1) < nums@.len() ==> nums@[j as int] <= nums@[(j + 1) as int],
                    exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
                decreases j
            {
                /* code modified by LLM (iteration 1): added bounds assertions and fixed swapping */
                assert(j > 0);
                assert(j < nums.len());
                assert(j - 1 < nums.len());
                
                let temp_prev = nums[j - 1];
                let temp_curr = nums[j];
                nums.set(j - 1, temp_curr);
                nums.set(j, temp_prev);
                j -= 1;
                
                /* code modified by LLM (iteration 1): prove invariants are maintained after swap */
                assert(sorted_between(nums@, 0, j as int));
                assert(exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@));
            }
        }
    }
}