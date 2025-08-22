use vstd::prelude::*;

verus! {
    spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> (result:bool) {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
    }
    // pure-end

    spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> (result:bool) {
        &&& r.len() == s.len()
        &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }
    // pure-end

    /* code modified by LLM (iteration 1): Added helper spec function to count occurrences in sequence */
    spec fn count_occurrences(s: Seq<u32>, val: u32) -> nat {
        s.filter(|x: u32| x == val).len()
    }

    //IMPL test1
    fn test1(nums: &mut Vec<u32>)
        // post-conditions-start
        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
        // post-conditions-end
    {
        let ghost original = nums@;
        let n = nums.len();
        
        for i in 1..n
            invariant
                sorted_between(nums@, 0, i as int),
                nums@.len() == original.len(),
                /* code modified by LLM (iteration 4): Added explicit trigger annotation to fix quantifier inference error */
                forall|j: int| 0 <= j < i ==> exists|k: int| 0 <= k < original.len() && #[trigger] nums@[j] == #[trigger] original[k],
                /* code modified by LLM (iteration 1): Changed count to count_occurrences helper function */
                forall|val: u32| count_occurrences(original, val) == count_occurrences(nums@, val),
        {
            let key = nums[i];
            let mut j = i;
            
            /* code modified by LLM (iteration 3): Added decreases clause to prove loop termination */
            while j > 0 && nums[j - 1] > key
                invariant
                    j <= i,
                    nums@.len() == original.len(),
                    /* code modified by LLM (iteration 1): Changed count to count_occurrences helper function */
                    forall|val: u32| count_occurrences(original, val) == count_occurrences(nums@, val),
                    sorted_between(nums@, 0, j as int),
                    sorted_between(nums@, (j + 1) as int, (i + 1) as int),
                    /* code modified by LLM (iteration 1): Cast j to int for sequence indexing */
                    j < i ==> nums@[j as int] == key,
                    forall|k: int| j < k <= i ==> nums@[k] > key,
                decreases j
            {
                /* code modified by LLM (iteration 2): Fixed borrowing issue by storing value before mutation */
                let temp_val = nums[j - 1];
                nums.set(j, temp_val);
                j -= 1;
            }
            
            nums.set(j, key);
        }
        
        // The reordering witness - identity permutation since we sorted in place
        let ghost reorder_seq = Seq::new(original.len(), |i: int| i);
        
        assert(is_reorder_of(reorder_seq, nums@, original)) by {
            assert(reorder_seq.len() == nums@.len());
            assert(forall|i: int| 0 <= i < reorder_seq.len() ==> 0 <= reorder_seq[i] < reorder_seq.len());
            assert(forall|i: int, j: int| 0 <= i < j < reorder_seq.len() ==> reorder_seq[i] != reorder_seq[j]);
        }
    }
}

fn main() {}