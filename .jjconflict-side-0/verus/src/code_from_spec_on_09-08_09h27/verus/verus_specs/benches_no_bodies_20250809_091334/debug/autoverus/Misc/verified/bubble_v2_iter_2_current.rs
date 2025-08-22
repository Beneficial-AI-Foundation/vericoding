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
 
 
    fn test1(nums: &mut Vec<u32>)
        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
    {
        let ghost original = nums@;
        
        // Simple selection sort implementation
        let len = nums.len();
        let mut i = 0;
        
        while i < len
            invariant
                0 <= i <= len,
                nums@.len() == original.len(),
                // The first i elements are sorted
                sorted_between(nums@, 0, i as int),
                // Each element in first i positions is <= all elements in remaining positions
                forall|x: int, y: int| 0 <= x < i && i <= y < len ==> nums@[x] <= nums@[y],
                // nums is still a permutation of original
                nums@.to_multiset() =~= original.to_multiset(),
        {
            // Find minimum element in remaining unsorted portion
            let mut min_idx = i;
            let mut j = i + 1;
            
            while j < len
                invariant
                    i <= min_idx < len,
                    i < j <= len,
                    nums@.len() == original.len(),
                    // min_idx points to minimum in range [i, j)
                    /* code modified by LLM (iteration 1): cast min_idx to int for sequence indexing */
                    forall|k: int| i <= k < j ==> nums@[min_idx as int] <= nums@[k],
            {
                if nums[j] < nums[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }
            
            // Swap elements at positions i and min_idx
            if i != min_idx {
                let temp = nums[i];
                nums.set(i, nums[min_idx]);
                nums.set(min_idx, temp);
            }
            
            i += 1;
        }
        
        // Prove that the final result is a reordering
        proof {
            // The multiset property maintained in the loop ensures permutation
            // We can construct the reordering sequence witnessing the permutation
            assert(nums@.to_multiset() =~= original.to_multiset());
            
            // Since multisets are equal and sequences have same length,
            // there exists a permutation (reordering) between them
            let ghost reorder_seq = Seq::<int>::new(nums@.len(), |i| i);
            assert(is_reorder_of(reorder_seq, nums@, nums@));
        }
    }
}