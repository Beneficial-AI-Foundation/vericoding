// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, aa: Seq<int>) -> bool {
    n >= 2 &&
    aa.len() == n - 1 &&
    forall|i: int| 0 <= i < aa.len() ==> #[trigger] aa[i] >= 1 && #[trigger] aa[i] < i + 2
}

spec fn subordinate_count(aa: Seq<int>, boss_id: int) -> int {
    Set::new(|j: int| 0 <= j < aa.len() && aa[j] == boss_id).len() as int
}

spec fn valid_output(n: int, aa: Seq<int>, result: Seq<int>) -> bool {
    result.len() == n &&
    forall|i: int| 0 <= i < n ==> #[trigger] result[i] >= 0 &&
    forall|i: int| 0 <= i < n ==> #[trigger] result[i] == subordinate_count(aa, i + 1)
}
// </vc-preamble>

// <vc-helpers>
spec fn count_for_prefix(aa: Seq<int>, prefix_len: int, boss_id: int) -> int
    decreases prefix_len
{
    if prefix_len <= 0 {
        0
    } else {
        (if aa[prefix_len - 1] == boss_id { 1 } else { 0 }) + count_for_prefix(aa, prefix_len - 1, boss_id)
    }
}

/* helper modified by LLM (iteration 2): fixed call to non-existent lemma with standard library equivalent */
proof fn lemma_count_is_subordinate(aa: Seq<int>)
    ensures
        forall|k: int| #[trigger] subordinate_count(aa, k) == count_for_prefix(aa, aa.len(), k),
    decreases aa.len(),
{
    if aa.len() > 0 {
        let prefix = aa.subrange(0, aa.len() - 1);
        lemma_count_is_subordinate(prefix);
        assert forall|k: int| subordinate_count(aa, k) == count_for_prefix(aa, aa.len(), k) by {
            let s_full = Set::new(|j: int| 0 <= j < aa.len() && aa[j] == k);
            let s_prefix = Set::new(|j: int| 0 <= j < prefix.len() && prefix[j] == k);
            let last_idx = aa.len() - 1;
            let last_val = aa.last();

            assert forall |j: int| s_full.contains(j) <==> (s_prefix.contains(j) || (j == last_idx && last_val == k)) by { }

            if last_val == k {
                assert(!s_prefix.contains(last_idx));
                lemma_len_insert(s_prefix, last_idx);
                assert(s_full.len() == s_prefix.len() + 1);
            } else {
                assert(s_full.len() == s_prefix.len());
            }
            assert(subordinate_count(aa, k) == subordinate_count(prefix, k) + if last_val == k { 1 } else { 0 });
            assert(count_for_prefix(aa, aa.len(), k) == count_for_prefix(prefix, prefix.len(), k) + if last_val == k { 1 } else { 0 });
            assert(subordinate_count(prefix, k) == count_for_prefix(prefix, prefix.len(), k));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, aa: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(n as int, aa@.map(|i, x| x as int))
    ensures valid_output(n as int, aa@.map(|i, x| x as int), result@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): declared aa_spec as ghost to allow spec types */
    let n_usize = n as usize;
    let mut result = vec![0i8; n_usize];

    ghost let aa_spec = aa@.map(|_, x| x as int);

    let mut i: usize = 0;
    while i < (n - 1) as usize
        invariant
            0 <= i <= (n-1) as usize,
            result.len() == n_usize,
            aa_spec == aa@.map(|_, x| x as int),
            forall|k: int| 0 <= k < n as int ==> result@[k] >= 0,
            forall|k: int| 0 <= k < n as int ==>
                (result@[k] as int) == count_for_prefix(aa_spec, i as int, k + 1),
    {
        let boss_id = aa[i];
        let boss_index = (boss_id - 1) as usize;

        proof {
            let i_int = i as int;
            let n_int = n as int;
            let result_after = result@.set(boss_index as int, result@[boss_index] + 1);

            assert forall |k: int| 0 <= k < n_int implies
                (result_after[k] as int) == count_for_prefix(aa_spec, i_int + 1, k + 1)
            by {
                let boss_id_at_i = aa_spec[i_int];
                let count_after = count_for_prefix(aa_spec, i_int + 1, k + 1);
                let count_before = count_for_prefix(aa_spec, i_int, k + 1);
                assert(count_after == count_before + if boss_id_at_i == k + 1 { 1 } else { 0 });

                if (boss_id - 1) as int == k {
                    assert(result@[k] as int == count_before);
                    assert(result_after[k] as int == result@[k] as int + 1);
                    assert(boss_id as int == k + 1);
                    assert(aa_spec[i_int] == boss_id as int);
                    assert(boss_id_at_i == k + 1);
                } else {
                    assert(result@[k] as int == count_before);
                    assert(result_after[k] as int == result@[k] as int);
                    assert(boss_id as int != k + 1);
                    assert(aa_spec[i_int] == boss_id as int);
                    assert(boss_id_at_i != k + 1);
                }
            }
        }

        let current_count = result[boss_index];
        result.set(boss_index, current_count + 1);

        i = i + 1;
    }

    proof {
        lemma_count_is_subordinate(aa_spec);
    }

    result
}
// </vc-code>


}

fn main() {}