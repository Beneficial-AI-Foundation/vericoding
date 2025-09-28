use vstd::prelude::*;

verus! {

/**
 * Find negative numbers from an array of numbers
 **/

spec fn is_negative(n: int) -> bool {
    n < 0
}

// <vc-helpers>
proof fn lemma_seq_push_index_preserve<T>(s: Seq<T>, x: T, k: int)
    requires
        0 <= k < s.len(),
    ensures
        #[trigger] (s.push(x))[k] == s[k]
{
    assert((s.push(x))[k] == s[k]);
}

proof fn lemma_seq_push_index_last<T>(s: Seq<T>, x: T)
    ensures
        #[trigger] (s.push(x))[s.len()] == x
{
    assert((s.push(x))[s.len()] == x);
}
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &[int]) -> (negative_list: Vec<int>)
    ensures
        // All numbers in the output are negative and exist in the input
        forall|i: int| 0 <= i < negative_list.len() ==> 
            is_negative(negative_list[i]) && exists|j: int| 0 <= j < arr.len() && arr[j] == negative_list[i],
        // All negative numbers in the input are in the output
        forall|i: int| 0 <= i < arr.len() && is_negative(arr[i]) ==> 
            exists|j: int| 0 <= j < negative_list.len() && negative_list[j] == arr[i],
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<int> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|k: int| 0 <= k < res.len() ==>
                is_negative(res@[k]) &&
                exists|j: int| 0 <= j < i && #[trigger] arr[j] == res@[k],
            forall|j: int| 0 <= j < i && is_negative(#[trigger] arr[j]) ==>
                exists|k: int| 0 <= k < res.len() && #[trigger] res@[k] == arr[j],
    {
        let x = arr[i];

        if x < 0 {
            let old_len = res.len();
            let old_seq = res@;
            let old_i = i;

            proof {
                // Freeze properties for old_seq and old_i
                assert_forall_by(|k: int| {
                    requires(0 <= k && k < old_len);
                    ensures(is_negative(old_seq[k]) &&
                        exists|j0: int| 0 <= j0 && j0 < old_i && #[trigger] arr[j0] == old_seq[k]);
                    assert(0 <= k && k < res.len());
                    assert(is_negative(res@[k]) &&
                        exists|j1: int| 0 <= j1 && j1 < i && #[trigger] arr[j1] == res@[k]);
                    assert(res@[k] == old_seq[k]);
                });
                assert_forall_by(|j: int| {
                    requires(0 <= j && j < old_i && is_negative(#[trigger] arr[j]));
                    ensures(exists|k0: int| 0 <= k0 && k0 < old_len && #[trigger] old_seq[k0] == arr[j]);
                    let k0 = choose|k0: int| 0 <= k0 && k0 < res.len() && #[trigger] res@[k0] == arr[j];
                    assert(0 <= k0 && k0 < old_len);
                    assert(old_seq[k0] == res@[k0]);
                });
            }

            i = i + 1;
            res.push(x);

            proof {
                assert(res@ == old_seq.push(x));
                // Re-establish first invariant
                assert_forall_by(|k: int| {
                    requires(0 <= k && k < res.len());
                    ensures(is_negative(res@[k]) &&
                        exists|j0: int| 0 <= j0 && j0 < i && #[trigger] arr[j0] == res@[k]);
                    if k < old_len {
                        lemma_seq_push_index_preserve(old_seq, x, k);
                        assert(res@[k] == old_seq[k]);
                        assert(is_negative(old_seq[k]) &&
                            exists|j1: int| 0 <= j1 && j1 < old_i && #[trigger] arr[j1] == old_seq[k]);
                        let j1 = choose|j1: int| 0 <= j1 && j1 < old_i && #[trigger] arr[j1] == old_seq[k];
                        assert(j1 < i);
                        assert(arr[j1] == res@[k]);
                    } else {
                        assert(k == old_len);
                        lemma_seq_push_index_last(old_seq, x);
                        assert(res@[k] == x);
                        assert(is_negative(x));
                        let j_new = (i as int) - 1;
                        assert(j_new == old_i);
                        assert(0 <= j_new && j_new < i);
                        assert(arr[j_new] == x);
                    }
                });
                // Re-establish second invariant
                assert_forall_by(|j: int| {
                    requires(0 <= j && j < i && is_negative(#[trigger] arr[j]));
                    ensures(exists|k0: int| 0 <= k0 && k0 < res.len() && #[trigger] res@[k0] == arr[j]);
                    if j < old_i {
                        let k0 = choose|k0: int| 0 <= k0 && k0 < old_len && #[trigger] old_seq[k0] == arr[j];
                        assert(0 <= k0 && k0 < res.len());
                        lemma_seq_push_index_preserve(old_seq, x, k0);
                        assert(res@[k0] == old_seq[k0]);
                    } else {
                        assert(j == old_i);
                        assert(arr[j] == x);
                        let k_new = old_len;
                        assert(0 <= k_new && k_new < res.len());
                        lemma_seq_push_index_last(old_seq, x);
                        assert(res@[k_new] == x);
                    }
                });
// </vc-code>

fn main() {}

}