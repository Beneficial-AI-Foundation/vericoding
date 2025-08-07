use vstd::prelude::*;

verus! {

// Helper function to check if a list has no duplicates
spec fn has_no_duplicates<T>(lst: Seq<T>) -> bool {
    forall|i: int, j: int| #![trigger lst[i], lst[j]] 0 <= i < j < lst.len() ==> lst[i] != lst[j]
}

// Helper function to check if all elements of nums1 are in nums2
spec fn all_in<T>(nums1: Seq<T>, nums2: Seq<T>) -> bool {
    forall|i: int| #![trigger nums1[i]] 0 <= i < nums1.len() ==> exists|j: int| #![trigger nums2[j]] 0 <= j < nums2.len() && nums1[i] == nums2[j]
}

// Precondition specification
spec fn next_greater_element_precond(nums1: Seq<i32>, nums2: Seq<i32>) -> bool {
    has_no_duplicates(nums1) &&
    has_no_duplicates(nums2) &&
    all_in(nums1, nums2)
}

// Helper function to find index of element in sequence
spec fn find_index_of<T>(seq: Seq<T>, val: T) -> Option<int> {
    if exists|i: int| #![trigger seq[i]] 0 <= i < seq.len() && seq[i] == val {
        Some(choose|i: int| #![trigger seq[i]] 0 <= i < seq.len() && seq[i] == val)
    } else {
        None
    }
}

// Helper function to find next greater element from a given position
spec fn find_next_greater(nums2: Seq<i32>, start_idx: int, val: i32) -> Option<i32> {
    if exists|k: int| #![trigger nums2[k]] start_idx < k < nums2.len() && nums2[k] > val {
        Some(nums2[choose|k: int| #![trigger nums2[k]] start_idx < k < nums2.len() && nums2[k] > val])
    } else {
        None
    }
}

// Postcondition specification
spec fn next_greater_element_postcond(nums1: Seq<i32>, nums2: Seq<i32>, result: Seq<i32>) -> bool {
    result.len() == nums1.len() &&
    
    (forall|i: int| #![trigger nums1[i], result[i]] 0 <= i < nums1.len() ==> {
        let val = nums1[i];
        let result_val = result[i];
        
        match find_index_of(nums2, val) {
            None => false,
            Some(idx) => {
                match find_next_greater(nums2, idx, val) {
                    None => result_val == -1,
                    Some(next_val) => result_val == next_val
                }
            }
        }
    }) &&
    
    (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
        let val = result[i];
        val == -1 || exists|j: int| #![trigger nums2[j]] 0 <= j < nums2.len() && nums2[j] == val
    })
}

fn next_greater_element(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: Vec<i32>)
    requires
        next_greater_element_precond(nums1@, nums2@)
    ensures
        result@.len() == nums1@.len(),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < nums1.len()
        invariant
            0 <= i <= nums1.len(),
            result.len() == i,
        decreases nums1.len() - i,
    {
        let val = nums1[i];
        let mut next_greater = -1;
        
        // Find position of val in nums2
        let mut val_pos = nums2.len();
        let mut j: usize = 0;
        while j < nums2.len()
            invariant
                0 <= j <= nums2.len(),
                val_pos == nums2.len() || (val_pos < nums2.len() && nums2[val_pos as int] == val),
            decreases nums2.len() - j,
        {
            if nums2[j] == val {
                val_pos = j;
                break;
            }
            j += 1;
        }
        
        // Find next greater element after val_pos
        if val_pos < nums2.len() {
            let mut k: usize = val_pos + 1;
            while k < nums2.len()
                invariant
                    val_pos < nums2.len(),
                    val_pos + 1 <= k <= nums2.len(),
                decreases nums2.len() - k,
            {
                if nums2[k] > val {
                    next_greater = nums2[k];
                    break;
                }
                k += 1;
            }
        }
        
        result.push(next_greater);
        i += 1;
    }
    
    result
}

}

fn main() {}