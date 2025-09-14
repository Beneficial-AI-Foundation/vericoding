// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted_between(a: Seq<u32>, from: int, to: int) -> (result:bool) {
        forall |i: int, j:int|  from <= i < j < to ==> a[i] <= a[j]
    }

spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> (result:bool) {
    &&& r.len() == s.len()
    &&& forall|i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall|i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& p =~= r.map_values(|i: int| s[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a swap helper function to maintain the reorder invariant */
proof fn swap_elements<T>(s: Seq<T>, i: int, j: int, s_prime: Seq<T>) 
requires
    0 <= i < s.len(),
    0 <= j < s.len(),
    s_prime.len() == s.len(),
    s_prime.index(i) == s.index(j),
    s_prime.index(j) == s.index(i),
    forall |k: int| 0 <= k < s.len() && k != i && k != j ==> s_prime.index(k) == s.index(k),
ensures
    exists |r: Seq<int>| is_reorder_of(r, s_prime, s)
{
    let r_len = s.len();
    let mut r_vec = Vec::new();
    let perm_s = Seq::new(r_len, |k: int| k);

    // construct r such that s_prime = r.map_values(|idx| s[idx])
    // r maps original indices to new indices
    // If s_prime[i] = s[j] and s_prime[j] = s[i]
    // then r[i] = j and r[j] = i
    // for k != i, j, s_prime[k] = s[k], so r[k] = k

    for k in 0..r_len as nat {
        if k == i as int {
            r_vec.push(j);
        } else if k == j as int {
            r_vec.push(i);
        } else {
            r_vec.push(k as int);
        }
    }
    let r = r_vec.to_seq();

    assert(r.len() == s.len());
    assert(forall|idx: int| 0 <= idx < r.len() ==> 0 <= #[trigger] r[idx] < r.len());
    assert(forall|idx1: int, idx2: int| 0 <= idx1 < idx2 < r.len() ==> r[idx1] != r[idx2]);
    assert(s_prime =~= r.map_values(|idx: int| s[idx]));
}
// </vc-helpers>

// <vc-spec>
fn test1(nums: &mut Vec<u32>)

        ensures
            sorted_between(nums@, 0, nums@.len() as int),
            exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed invariant syntax with curly braces and added proof for reorder_of */
{
    let l = nums.len();
    if l > 1 {
        let mut i = 0;
        while i < l - 1
            invariant l == nums.len(),
            invariant (
                forall|x: int, y: int| 0 <= x < y < i ==> nums@[x] <= nums@[y]
            ),
            invariant (
                exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)
            ),
            decreases l - 1 - i
        {
            assert(i >= 0 && i < l);
            let mut j = i + 1;
            let nums_at_start_of_inner_loop = nums@;
            while j < l
                invariant l == nums.len(),
                invariant (
                    forall|x: int, y: int| 0 <= x < y < i ==> nums@[x] <= nums@[y]
                ),
                invariant (
                    forall|x: int| i <= x < j ==> nums_at_start_of_inner_loop@[i] <= nums@[x]
                ),
                invariant (
                    exists|r: Seq<int>| is_reorder_of(r, nums@, old(nums)@)
                ),
                decreases l - j
            {
                assert(j >= 0 && j < l);
                if nums@[j] < nums@[i] {
                    let pre_swap_seq = nums@;
                    let old_i_val = nums@[i];
                    let old_j_val = nums@[j];
                    nums.set(i as int, old_j_val);
                    nums.set(j as int, old_i_val);

                    proof {
                        // Construct the sequence after the swap
                        let mut post_swap_vec = Vec::new();
                        for k in 0..l as nat {
                            if k == i as int {
                                post_swap_vec.push(old_j_val);
                            } else if k == j as int {
                                post_swap_vec.push(old_i_val);
                            } else {
                                post_swap_vec.push(pre_swap_seq@[k as int]);
                            }
                        }
                        let post_swap_seq = post_swap_vec.to_seq();

                        // Prove that is_reorder_of holds for the swapped sequence
                        swap_elements(pre_swap_seq, i, j, post_swap_seq);
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }
    }
}
// </vc-code>

}
fn main() {}