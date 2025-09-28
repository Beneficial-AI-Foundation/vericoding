// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains(s: Seq<i8>, val: i8) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == val
}

proof fn lemma_insert_sorted_preserves_uniqueness(s: Seq<i8>, val: i8, pos: int)
    requires
        0 <= pos <= s.len(),
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j],
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s[i] != s[j],
        forall|i: int| 0 <= i < pos ==> s[i] < val,
        forall|i: int| pos <= i < s.len() ==> val < s[i],
    ensures
        forall|i: int, j: int| 0 <= i < j < s.insert(pos, val).len() ==> s.insert(pos, val)[i] < s.insert(pos, val)[j],
        forall|i: int, j: int| 0 <= i < s.insert(pos, val).len() && 0 <= j < s.insert(pos, val).len() && i != j ==> s.insert(pos, val)[i] != s.insert(pos, val)[j],
{
    let new_s = s.insert(pos, val);
    assert forall|i: int, j: int| 0 <= i < j < new_s.len() implies new_s[i] < new_s[j] by {
        if i < pos && j == pos {
            assert(new_s[i] == s[i]);
            assert(new_s[j] == val);
            assert(s[i] < val);
        } else if i < pos && j > pos {
            assert(new_s[i] == s[i]);
            assert(new_s[j] == s[j - 1]);
            assert(s[i] < s[j - 1]);
        } else if i == pos && j > pos {
            assert(new_s[i] == val);
            assert(new_s[j] == s[j - 1]);
            assert(val < s[j - 1]);
        } else if i > pos && j > pos {
            assert(new_s[i] == s[i - 1]);
            assert(new_s[j] == s[j - 1]);
            assert(s[i - 1] < s[j - 1]);
        } else {
            assert(new_s[i] == s[i]);
            assert(new_s[j] == s[j]);
            assert(s[i] < s[j]);
        }
    }
}

fn binary_search_insert(sorted: &Vec<i8>, val: i8) -> (pos: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] < sorted@[j],
    ensures
        0 <= pos <= sorted@.len(),
        forall|i: int| 0 <= i < pos ==> sorted@[i] < val,
        forall|i: int| pos <= i < sorted@.len() ==> val < sorted@[i],
{
    let mut left: usize = 0;
    let mut right: usize = sorted.len();
    
    while left < right
        invariant
            0 <= left <= right <= sorted@.len(),
            forall|i: int| 0 <= i < left ==> sorted@[i] < val,
            forall|i: int| right <= i < sorted@.len() ==> val < sorted@[i],
        decreases right - left,
    {
        let mid = left + (right - left) / 2;
        if sorted[mid] < val {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    left
}
// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i8>) -> (result: Vec<i8>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> #[trigger] result@[i] < #[trigger] result@[j],

        forall|i: int| 0 <= i < result@.len() ==> exists|j: int| 0 <= j < arr@.len() && #[trigger] result@[i] == #[trigger] arr@[j],

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> #[trigger] result@[i] != #[trigger] result@[j],

        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < result@.len() && #[trigger] arr@[i] == #[trigger] result@[j],
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr@.len(),
            forall|j: int, k: int| 0 <= j < k < result@.len() ==> result@[j] < result@[k],
            forall|j: int, k: int| 0 <= j < result@.len() && 0 <= k < result@.len() && j != k ==> result@[j] != result@[k],
            forall|j: int| 0 <= j < result@.len() ==> exists|k: int| 0 <= k < i && arr@[k] == result@[j],
            forall|j: int| 0 <= j < i ==> contains(result@, arr@[j]),
        decreases arr@.len() - i,
    {
        let val = arr[i];
        let mut found = false;
        let mut j: usize = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result@.len(),
                found ==> exists|k: int| 0 <= k < j && result@[k] == val,
                !found ==> forall|k: int| 0 <= k < j ==> result@[k] != val,
            decreases result@.len() - j,
        {
            if result[j] == val {
                found = true;
                proof {
                    assert(result@[j as int] == val);
                }
                break;
            }
            j = j + 1;
        }
        
        if !found {
            let pos = binary_search_insert(&result, val);
            proof {
                lemma_insert_sorted_preserves_uniqueness(result@, val, pos as int);
            }
            result.insert(pos, val);
        }
        
        i = i + 1;
    }
    
    assert forall|k: int| 0 <= k < arr@.len() implies contains(result@, arr@[k]) by {
        assert(forall|j: int| 0 <= j < arr@.len() ==> contains(result@, arr@[j]));
    }
    
    assert forall|k: int| 0 <= k < arr@.len() implies exists|j: int| 0 <= j < result@.len() && arr@[k] == result@[j] by {
        assert forall|k: int| 0 <= k < arr@.len() implies contains(result@, arr@[k]) by {};
    }
    
    result
}
// </vc-code>

}
fn main() {}