// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn count_true_le_len(s: Seq<bool>)
    ensures count_true(s) <= s.len()
    decreases s.len()
{
    if s.len() > 0 {
        count_true_le_len(s.skip(1));
    }
}

/* helper modified by LLM (iteration 4): added proof logic for inductive step */
proof fn lemma_count_true_append(s1: Seq<bool>, s2: Seq<bool>)
    ensures count_true(s1 + s2) == count_true(s1) + count_true(s2)
    decreases s1.len()
{
    if s1.len() > 0 {
        assert((s1 + s2).skip(1) == s1.skip(1) + s2);
        lemma_count_true_append(s1.skip(1), s2);
    }
}

/* helper modified by LLM (iteration 5): added explicit case analysis in loop proof */
fn count_true_exec(condition: &Vec<bool>) -> (result: usize)
    ensures result as int == count_true(condition@)
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < condition.len()
        invariant
            0 <= i <= condition.len(),
            count as int == count_true(condition@.take(i as int)),
        decreases condition.len() - i
    {
        proof {
            let s = condition@;
            let i_int = i as int;
            
            count_true_le_len(s.take(i_int));

            assert(s.take(i_int + 1) == s.take(i_int) + seq![s[i_int]]);
            lemma_count_true_append(s.take(i_int), seq![s[i_int]]);
            
            if s[i_int] {
                assert(count_true(seq![s[i_int]]) == 1);
                assert(count_true(s.take(i_int + 1)) == count_true(s.take(i_int)) + 1);
            } else {
                assert(count_true(seq![s[i_int]]) == 0);
                assert(count_true(s.take(i_int + 1)) == count_true(s.take(i_int)));
            }
        }

        if condition[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    assert(condition@.take(i as int) == condition@);
    count
}
// </vc-helpers>

// <vc-spec>
spec fn count_true(condition: Seq<bool>) -> int 
    decreases condition.len()
{
    if condition.len() == 0 {
        0int
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true(condition.skip(1))
    }
}

fn extract(condition: Vec<bool>, arr: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == arr.len(),
        count_true(condition@) >= 0,
    ensures
        result.len() == count_true(condition@),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == arr[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): resubmitting to focus on fixing the failing helper function */
    let num_true = count_true_exec(&condition);
    proof {
        count_true_le_len(condition@);
    }
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < num_true
        invariant
            num_true as int == count_true(condition@),
            num_true <= arr.len(),
            0 <= i <= num_true,
            result.len() == i,
            result@ == arr@.subrange(0, i as int),
        decreases num_true - i
    {
        result.push(arr[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}