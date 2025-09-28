// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [No changes needed. Retaining previous iteration's helper.] */
proof fn lemma_swap_permutation<T>(s: &mut Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.len() == old(s).len(),
        s@ =~= ({let mut s_next = old(s); s_next = s_next.update(i, old(s).index(j)); s_next = s_next.update(j, old(s).index(i)); s_next}),
{
    // No specific proof steps are needed here, as the `update` operations are directly asserted by the `ensures` clause.
}

proof fn lemma_swap_to_seq<T>(v: &mut Vec<T>, i: int, j: int)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures
        v.len() == old(v).len(),
        v.proof_seq() =~= ({let mut s_next = old(v).proof_seq(); s_next = s_next.update(i, old(v).proof_seq().index(j)); s_next = s_next.update(j, old(v).proof_seq().index(i)); s_next}),
{
    v.swap(i as usize, j as usize);
}
// </vc-helpers>

// <vc-spec>
fn argpartition(a: Vec<i8>, kth: usize) -> (indices: Vec<usize>)
    requires 
        a.len() > 0,
        kth < a.len(),
    ensures
        /* The indices form a valid permutation of 0..n-1 */
        indices.len() == a.len(),
        /* Partition property: all elements before kth position are ≤ kth element */
        forall|i: int| 0 <= i < kth ==> a@[#[trigger] indices@[i] as int] <= a@[#[trigger] indices@[kth as int] as int],
        /* Partition property: all elements after kth position are ≥ kth element */
        forall|i: int| kth < i && i < indices.len() ==> a@[#[trigger] indices@[kth as int] as int] <= a@[#[trigger] indices@[i] as int],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixed a syntax error in the invariant by replacing missing comma.] */
{
    let n = a.len();
    let mut indices: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            indices.len() == i,
            forall|j: int| 0 <= j < i ==> indices.view()[j] == j,
        decreases n - i
    {
        indices.push(i);
        i += 1;
    }

    let mut arr = a.clone();
    let mut left: usize = 0;
    let mut right: usize = n - 1;

    while left <= right
        invariant
            left <= right + 1,
            left <= n,
            right < n,
            indices.len() == n,
            arr.len() == n,

            // Invariant 1: Permutation of initial indices
            ({let mut s = Seq::<usize>::new();
              let mut k = 0;
              while k < n
                  invariant
                      k <= n,
                      s.len() == k,
                      forall|l: int| 0 <= l < k ==> s@[l] == l,
                  decreases n - k
              {
                  s = s.push(k as usize);
                  k += 1;
              }
              s}).permutation_of(indices@),

            // Invariant 2: elements smaller than pivot are to the left of p
            forall|k: int| (0 <= k < left as int && k < n as int && left as int <= right as int + 1) ==> 
                (arr.view()[indices.view()[k]] <= arr.view()[indices.view()[kth as int]]),

            // Invariant 3: elements larger than pivot are to the right of p
            forall|k: int| (k > right as int && k < n as int && left as int <= right as int + 1) ==> 
                (arr.view()[indices.view()[kth as int]] <= arr.view()[indices.view()[k]]),
            
            // Invariant 4: kth element is between left and right (inclusive)
            left <= kth && kth <= right || kth < left || kth > right,
            
        decreases right - left
    {
        let pivot_index = kth;
        let pivot_value = arr.view()[indices.view()[pivot_index as int]];

        // Move left pointer past elements smaller than pivot
        while left < right && arr.view()[indices.view()[left as int]] < pivot_value
            invariant
                left <= right,
                left < n,
                right < n,
                indices.len() == n,
                arr.len() == n,
                left <= pivot_index || pivot_index < left || pivot_index > right,
                // All elements before current `left` are less than pivot_value
                forall|k: int| (0 <= k < left as int) ==> (arr.view()[indices.view()[k]] < pivot_value),
                ({let mut s = Seq::<usize>::new();
                  let mut k = 0;
                  while k < n
                      invariant
                          k <= n,
                          s.len() == k,
                          forall|l: int| 0 <= l < k ==> s@[l] == l,
                      decreases n - k
                  {
                      s = s.push(k as usize);
                      k += 1;
                  }
                  s}).permutation_of(indices@),
            decreases right - left
        {
            left += 1;
        }

        // Move right pointer past elements larger than pivot
        while left < right && arr.view()[indices.view()[right as int]] > pivot_value
            invariant
                left <= right,
                left < n,
                right < n,
                indices.len() == n,
                arr.len() == n,
                left <= pivot_index || pivot_index < left || pivot_index > right,
                // All elements after current `right` are greater than pivot_value
                forall|k: int| (right as int < k && k < n as int) ==> (arr.view()[indices.view()[k]] > pivot_value),
                ({let mut s = Seq::<usize>::new();
                  let mut k = 0;
                  while k < n
                      invariant
                          k <= n,
                          s.len() == k,
                          forall|l: int| 0 <= l < k ==> s@[l] == l,
                      decreases n - k
                  {
                      s = s.push(k as usize);
                      k += 1;
                  }
                  s}).permutation_of(indices@),
            decreases right - left
        {
            right -= 1;
        }

        if left < right {
            let temp_idx = indices.view()[left as int];
            let temp_val = arr.view()[indices.view()[left as int]];
            
            proof {
                lemma_swap_permutation(&mut indices@, left as int, right as int);
            }
            indices.swap(left, right);
            

            left += 1;
            right -= 1;
        } else {
             if left == right && arr.view()[indices.view()[left as int]] == pivot_value {
                 break; // Already partitioned around this pivot
             }
        }
    }

    indices
}
// </vc-code>


}
fn main() {}