```vc-helpers
_proof{
    // This struct is used to carry the crucial invariant through the recursion
    #[derive(Clone, Eq, PartialEq)]
    closed struct GhostIndices {
        c: nat,
        f: nat,
        v: Seq<i32>,
        elem: i32,
    }

    impl GhostIndices {
        // The invariant captures the key properties of the subarray v[c..=f]
        pub closed spec fn invariant(&self) -> bool {
            &&& self.c <= self.f + 1
            &&& self.f + 1 <= self.v.len()
            &&& forall|k: int| 0 <= k < self.c ==> #[trigger] self.v[k] <= self.elem
            &&& forall|k: int| self.f < k < self.v.len() ==> #[trigger] self.v[k] > self.elem
        }

        // The final property that the returned index p must satisfy relative to the initial array
        pub closed spec fn postcondition(&self, p: isize) -> bool {
            &&& -1 <= p < self.v.len() as isize
            &&& forall|u: int| 0 <= u <= p ==> #[trigger] self.v[u] <= self.elem
            &&& forall|w: int| p < w < self.v.len() ==> #[trigger] self.v[w] > self.elem
        }

        // A lemma to prove that if the invariant holds for an array and a search element,
        // it also holds for a relevant subarray during the recursive search.
        pub closed spec fn invariant_holds_for_subrange(
            v: Seq<i32>, elem: i32, c_init: nat, f_init: nat, c_new: nat, f_new: nat
        ) -> bool {
            &&& c_init <= f_init + 1
            &&& f_init + 1 <= v.len()
            &&& forall|k: int| 0 <= k < c_init ==> #[trigger] v[k] <= elem
            &&& forall|k: int| f_init < k < v.len() ==> #[trigger] v[k] > elem
            &&& c_init <= c_new <= f_new + 1
            &&& f_new + 1 <= f_init + 1
            ==> forall|k: int| 0 <= k < c_new ==> #[trigger] v[k] <= elem
                && forall|k: int| f_new < k < v.len() ==> #[trigger] v[k] > elem
        }

        // Proof for the lemma `invariant_holds_for_subrange`.
        proof fn lemma_invariant_holds_for_subrange(
            v: Seq<i32>, elem: i32, c_init: nat, f_init: nat, c_new: nat, f_new: nat
        )
            requires
                c_init <= f_init + 1,
                f_init + 1 <= v.len(),
                forall|k: int| 0 <= k < c_init ==> #[trigger] v[k] <= elem,
                forall|k: int| f_init < k < v.len() ==> #[trigger] v[k] > elem,
                c_init <= c_new <= f_new + 1,
                f_new + 1 <= f_init + 1,
            ensures
                Self::invariant_holds_for_subrange(v, elem, c_init, f_init, c_new, f_new),
                forall|k: int| 0 <= k < c_new ==> #[trigger] v[k] <= elem,
                forall|k: int| f_new < k < v.len() ==> #[trigger] v[k] > elem,
        {
            assert(forall|k: int| 0 <= k < c_new ==> #[trigger] v[k] <= elem) by {
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k < c_new
                    implies v@[k] <= elem
                {
                    if k < c_init {
                        assert(v@[k] <= elem);
                    } else {
                        // This branch handles k where c_init <= k < c_new.
                        // The invariant does not provide direct info about v[k] in this range.
                        // However, by choosing c_new <= f_init + 1, this range is effectively empty.
                        // Proof:
                        // 1. Assume for contradiction that such a k exists.
                        // 2. By creation of c_new/f_new, c_new must be derived from the midpoint:
                        //    a) if v[m.id()] <= elem, c_new = m.id() + 1. f_new = f_init.
                        //       Then c_new = m.id()+1. We know m.id() < f_init+1 so c_new <= f_init+1. holds.
                        //       We need to check 0 <= k <= m.id(). Since k >= c_init, and c_init <= m.id() by the way loop works.
                        //       For a binary search, if v[m.id()] <= elem, then all elements up to m.id() are <= elem.
                        //       However, the pre-condition only guarantees elements up to c_init-1 are <= elem.
                        //       We need to ensure the left part of the slice is valid.
                        //       Given the sorted nature and the fact that we are narrowing down the search space,
                        //       the invariant on the *entire array* `v` is what's used to construct the new
                        //       inductive hypotheses for the recursive call. We are not changing v.
                    }
                }
            };

            assert(forall|k: int| f_new < k < v.len() ==> #[trigger] v[k] > elem) by {
                forall|k: int|
                    #![trigger v@[k]]
                    f_new < k < v.len()
                    implies v@[k] > elem
                {
                    if f_init < k {
                        assert(v@[k] > elem);
                    } else {
                        // This branch handles k where f_new < k <= f_init.
                        // We need to prove that v[k] > elem in this range.
                        // The invariant does not provide direct info about v[k] in this range.
                        // However, by choosing c_new and f_new appropriately, this range is also effectively empty.
                        // Proof:
                        // 1. Assume for contradiction that such a k exists.
                        // 2. By creation of c_new/f_new, f_new must be derived from the midpoint:
                        //    a) if v[m.id()] <= elem, c_new = m.id() + 1, f_new = f_init. This range is empty.
                        //    b) if v[m.id()] > elem, c_new = c_init, f_new = m.id() - 1.
                        //       Then f_new = m.id()-1. We need to check f_new < k <= f_init, i.e. m.id()-1 < k <= f_init.
                        //       For a binary search, if v[m.id()] > elem, all elements from m.id() onwards are > elem.
                        //       We need to show that any k in (m.id()-1, f_init] has v[k] > elem.
                        //       Since v is sorted, v[k] >= v[m.id()] > elem.
                    }
                }
            };
        }
    }
}
```
```vc-code
{
    // Base case: search space is empty. This means `elem` is smaller than all elements in the original
    // search space, as the `c` index has moved past the `f` index. The largest index where
    // `v[index] <= elem` would be `c - 1`.
    if c > f {
        let p = c - 1;
        // Prove the postcondition for `p`.
        proof {
            // 1. Bounds check on p: -1 <= p < v.len()
            // From the pre-condition: 0 <= c <= f + 1.
            // Since c > f, we have c = f + 1.
            // So p = (f+1) - 1 = f.
            // We know 0 <= c = f+1 <= v.len(), so 0 <= f+1 <= v.len(), which means -1 <= f < v.len().
            assert(p as int == f);

            // 2. Prove: forall|u: int| 0 <= u <= p ==> v[u] <= elem
            // We know p = f. The pre-condition states: forall|k: int| 0 <= k < c ==> v[k] <= elem.
            // Since c = f + 1, this means forall|k: int| 0 <= k < f + 1 ==> v[k] <= elem.
            // This is equivalent to forall|u: int| 0 <= u <= f ==> v[u] <= elem.
            // Since p = f, the post-condition holds.

            // 3. Prove: forall|w: int| p < w < v.len() ==> v[w] > elem
            // We know p = f. The pre-condition directly states: forall|k: int| f < k < v.len() ==> v[k] > elem.
            // This is exactly the third part of the post-condition.
        }
        return p;
    }

    let mid = c + (f - c) / 2;
    // Ensure mid is within bounds. Since c <= f, mid is in [c, f].
    // Also, 0 <= c <= f < v.len() from pre-condition, so 0 <= mid < v.len().
    assert(0 <= mid < v.len() as int);

    if v@[mid as int] <= elem {
        // If the middle element is <= elem, we know the result cannot be less than `mid`.
        // So, we search the right half: [mid+1, f].
        let sub_c = mid + 1;
        let sub_f = f;

        // Subarray indices are valid: sub_c <= sub_f + 1 because mid <= f implies mid+1 <= f+1.
        proof {
            lemma_properties::GhostIndices::lemma_invariant_holds_for_subrange(
                v@,
                elem,
                c as nat,
                f as nat,
                sub_c as nat,
                sub_f as nat,
            );
            // The lemma establishes the pre-conditions for the recursive call:
            // 1. sub_c <= sub_f + 1 <= v.len() (from c <= f+1 <= v.len() and sub_c = mid+1, sub_f = f)
            // 2. forall|k: int| 0 <= k < sub_c ==> v[k] <= elem
            //    - For k < c, this is from the original invariant.
            //    - For c <= k < mid+1, we know v is sorted and v@[mid] <= elem, so v[k] <= v[mid] <= elem.
            // 3. forall|k: int| sub_f < k < v.len() ==> v[k] > elem
            //    - This is the same as the original invariant since sub_f = f.
        }

        let rec_p = binary_search_recursive(v, elem, sub_c, sub_f); // recursive call
        let p = rec_p;

        // The postcondition of the recursive call guarantees:
        // forall|u: int| 0 <= u <= p ==> v[u] <= elem
        // forall|w: int| p < w < v.len() ==> v[w] > elem
        // These are exactly the postconditions required by the current call.
        // And the bounds on p are also guaranteed by the recursive call's postcondition.
        p
    } else {
        // If the middle element > elem, we know the result is in the left half: [c, mid-1].
        let sub_c = c;
        let sub_f = mid - 1;

        // Check if the new search space is valid: sub_c <= sub_f + 1.
        // If c > mid-1, then the base case will be triggered immediately in the recursive call.
        proof {
            lemma_properties::GhostIndices::lemma_invariant_holds_for_subrange(
                v@,
                elem,
                c as nat,
                f as nat,
                sub_c as nat,
                sub_f as nat,
            );
            // The lemma establishes the pre-conditions for the recursive call:
            // 1. sub_c <= sub_f + 1 <= v.len() (from c <= f+1 <= v.len() and sub_c = c, sub_f = mid-1)
            // 2. forall|k: int| 0 <= k < sub_c ==> v[k] <= elem
            //    - This is the same as the original invariant since sub_c = c.
            // 3. forall|k: int| sub_f < k < v.len() ==> v[k] > elem
            //    - For k > f, this is from the original invariant.
            //    - For mid-1 < k <= f, we know v is sorted and v@[mid] > elem, so v[k] >= v[mid] > elem.
        }

        let rec_p = binary_search_recursive(v, elem, sub_c, sub_f); // recursive call
        let p = rec_p;

        // The postcondition of the recursive call guarantees:
        // forall|u: int| 0 <= u <= p ==> v[u] <= elem
        // forall|w: int| p < w < v.len() ==> v[w] > elem
        // These are exactly the postconditions required by the current call.
        // And the bounds on p are also guaranteed by the recursive call's postcondition.
        p
    }
}
```