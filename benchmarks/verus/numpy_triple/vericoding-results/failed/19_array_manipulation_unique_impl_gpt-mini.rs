// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial helper lemma to satisfy top-level item requirement */
fn _empty_seq_properties() {
    proof {
        assert(true);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn has_no_duplicates(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

spec fn all_elements_from_input(result: Seq<i32>, input: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> #[trigger] input.contains(result[i])
}

spec fn all_distinct_elements_present(input: Seq<i32>, result: Seq<i32>) -> bool {
    forall|val: i32| input.contains(val) ==> #[trigger] result.contains(val)
}

fn numpy_unique(arr: Vec<i32>) -> (result: (usize, Vec<i32>))
    ensures
        is_sorted(result.1@),
        has_no_duplicates(result.1@),
        all_elements_from_input(result.1@, arr@),
        all_distinct_elements_present(arr@, result.1@),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): selection-minimum unique extraction with explicit counts and trigger annotations for quantifiers */
  {
    let mut rem = arr.clone();
    let mut res: Vec<i32> = Vec::new();

    while rem.len() > 0
        invariant
            all_elements_from_input(res@, arr@),
            has_no_duplicates(res@),
            is_sorted(res@),
            all_elements_from_input(rem@, arr@),
            forall|i: int, j: int| 0 <= i < res.len() && 0 <= j < rem.len() ==> res@[i] < rem@[j],
        decreases rem.len()
    {
        // find minimum m in rem
        let mut idx: usize = 1;
        let mut m: i32 = rem[0];
        while idx < rem.len()
            invariant
                0 <= idx <= rem.len(),
                forall|t: int| 0 <= t < idx ==> m <= rem@[t],
                exists|k: int| 0 <= k < idx && #[trigger] rem@[k] == m,
            decreases rem.len() - idx
        {
            let v: i32 = rem[idx];
            if v < m {
                m = v;
            }
            idx = idx + 1;
        }

        proof {
            // From inner invariant at exit (idx == rem.len()) we get m is a minimum and exists occurrence
            assert(forall|t: int| 0 <= t < rem.len() ==> m <= rem@[t]);
            assert(exists|k: int| 0 <= k < rem.len() && #[trigger] rem@[k] == m);

            // All elements of res are < every element of rem, so in particular they are < m
            assert(forall|i: int| 0 <= i < res.len() ==> res@[i] < m);
            assert(has_no_duplicates(res@));
            assert(is_sorted(res@));
        }

        res.push(m);

        // remove all occurrences of m from rem, while counting removals to prove strict decrease
        let mut new_rem: Vec<i32> = Vec::new();
        let mut r_idx: usize = 0;
        let mut removed_count: usize = 0;
        while r_idx < rem.len()
            invariant
                0 <= r_idx <= rem.len(),
                all_elements_from_input(new_rem@, arr@),
                forall|j: int| 0 <= j < new_rem.len() ==> exists|k: int| 0 <= k < r_idx && #[trigger] rem@[k] == new_rem@[j] && rem@[k] != m,
                removed_count + new_rem.len() == r_idx,
                0 <= removed_count <= r_idx,
            decreases rem.len() - r_idx
        {
            let v: i32 = rem[r_idx];
            if v != m {
                new_rem.push(v);
            } else {
                removed_count = removed_count + 1;
            }
            r_idx = r_idx + 1;
        }

        proof {
            // From loop invariants at exit (r_idx == rem.len())
            assert(removed_count + new_rem.len() == rem.len());
            assert(all_elements_from_input(new_rem@, arr@));

            // For every element of new_rem there exists k < rem.len() with rem[k] == new_rem[j] and rem[k] != m
            assert(forall|j: int| 0 <= j < new_rem.len() ==> exists|k: int| 0 <= k < rem.len() && #[trigger] rem@[k] == new_rem@[j] && rem@[k] != m);

            // Using minimality: m <= rem[t] for all t, and for those rem[k] != m we get m < rem[k]
            assert(forall|j: int| 0 <= j < new_rem.len() ==> m < new_rem@[j]);

            // Show that at least one element was removed: since rem contained m, some index equal to m was processed and counted
            assert(exists|k: int| 0 <= k < rem.len() && #[trigger] rem@[k] == m);
            // From removed_count + new_rem.len() == rem.len(), and the fact that elements equal to m are not added to new_rem,
            // we conclude removed_count > 0, hence new_rem.len() < rem.len()
            assert(removed_count > 0);
            assert(new_rem.len() < rem.len());

            // All elements of res (including newly pushed m) are < all elements of new_rem because res elements < m and m < new_rem[j]
            assert(forall|i: int, j: int| 0 <= i < res.len() && 0 <= j < new_rem.len() ==> res@[i] < new_rem@[j]);
        }

        rem = new_rem;
    }

    let size = res.len();
    (size, res)
  }
}
// </vc-code>


}
fn main() {}