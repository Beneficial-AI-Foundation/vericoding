// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(scores: Seq<int>) -> bool {
    scores.len() > 0 && scores.len() <= 100 &&
    forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores[i] >= 1 && #[trigger] scores[i] <= 100
}

spec fn sum_seq(scores: Seq<int>) -> int
    decreases scores.len()
{
    if scores.len() == 0 {
        0
    } else {
        scores[0] + sum_seq(scores.subrange(1, scores.len() as int))
    }
}

spec fn all_multiples_of_10(scores: Seq<int>) -> bool {
    forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores[i] % 10 == 0
}

spec fn is_smallest_non_multiple(scores: Seq<int>, value: int) -> bool {
    scores.contains(value) && 
    value % 10 != 0 &&
    forall|x: int| #[trigger] scores.contains(x) && x % 10 != 0 ==> value <= x
}

spec fn correct_result(scores: Seq<int>, result: int) -> bool {
    let total_sum = sum_seq(scores);
    if total_sum % 10 != 0 {
        result == total_sum
    } else if all_multiples_of_10(scores) {
        result == 0
    } else {
        exists|smallest_non_multiple: int| 
            is_smallest_non_multiple(scores, smallest_non_multiple) &&
            result == total_sum - smallest_non_multiple
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn sum_seq_bounds(scores: Seq<int>)
    requires
        scores.len() > 0,
        scores.len() <= 100,
        forall|i: int| 0 <= i < scores.len() ==> scores[i] >= 1 && scores[i] <= 100
    ensures
        sum_seq(scores) >= scores.len(),
        sum_seq(scores) <= scores.len() * 100
    decreases scores.len()
{
    if scores.len() == 1 {
        assert(sum_seq(scores) == scores[0]);
        assert(scores[0] >= 1 && scores[0] <= 100);
    } else {
        let rest = scores.subrange(1, scores.len() as int);
        sum_seq_bounds(rest);
        assert(sum_seq(scores) == scores[0] + sum_seq(rest));
    }
}

proof fn sum_seq_append(s1: Seq<int>, s2: Seq<int>)
    ensures sum_seq(s1 + s2) == sum_seq(s1) + sum_seq(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1 + s2 =~= s2);
    } else {
        let rest = s1.subrange(1, s1.len() as int);
        assert((s1 + s2).subrange(1, (s1 + s2).len() as int) =~= rest + s2);
        sum_seq_append(rest, s2);
    }
}

proof fn sum_without_element(scores: Seq<int>, idx: int)
    requires
        0 <= idx < scores.len()
    ensures
        sum_seq(scores.remove(idx)) == sum_seq(scores) - scores[idx]
{
    let before = scores.subrange(0, idx);
    let after = scores.subrange(idx + 1, scores.len() as int);
    let elem = seq![scores[idx]];
    
    assert(scores =~= before + elem + after);
    assert(scores.remove(idx) =~= before + after);
    
    sum_seq_append(before, elem + after);
    sum_seq_append(elem, after);
    sum_seq_append(before, after);
}
// </vc-helpers>

// <vc-spec>
fn solve(scores: Vec<i8>) -> (result: i8)
    requires valid_input(scores@.map(|i, x| x as int))
    ensures correct_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type error by using ghost for spec-only conversion */
    let ghost scores_seq = scores@.map(|j, x| x as int);
    
    let total_sum = {
        let mut sum: i8 = 0;
        let mut i: usize = 0;
        while i < scores.len()
            invariant
                0 <= i <= scores.len(),
                sum as int == sum_seq(scores@.map(|j, x| x as int).subrange(0, i as int))
            decreases scores.len() - i
        {
            sum = sum + scores[i];
            proof {
                let ghost seq1 = scores@.map(|j, x| x as int);
                assert(seq1.subrange(0, (i + 1) as int) =~=
                       seq1.subrange(0, i as int) + 
                       seq![seq1[i as int]]);
            }
            i = i + 1;
        }
        proof {
            assert(scores@.map(|j, x| x as int).subrange(0, scores.len() as int) =~= scores@.map(|j, x| x as int));
        }
        sum
    };
    
    if total_sum % 10 != 0 {
        return total_sum;
    }
    
    let mut smallest_non_multiple: Option<i8> = None;
    let mut i: usize = 0;
    
    while i < scores.len()
        invariant
            0 <= i <= scores.len(),
            smallest_non_multiple.is_none() ==> forall|j: int| 0 <= j < i ==> scores@.map(|k, x| x as int)[j] % 10 == 0,
            smallest_non_multiple.is_some() ==> scores@.map(|j, x| x as int).contains(smallest_non_multiple.unwrap() as int),
            smallest_non_multiple.is_some() ==> smallest_non_multiple.unwrap() as int % 10 != 0,
            smallest_non_multiple.is_some() ==> forall|j: int| 0 <= j < i && scores@.map(|k, x| x as int)[j] % 10 != 0 ==> 
                smallest_non_multiple.unwrap() as int <= scores@.map(|k, x| x as int)[j]
        decreases scores.len() - i
    {
        if scores[i] % 10 != 0 {
            if smallest_non_multiple.is_none() || scores[i] < smallest_non_multiple.unwrap() {
                smallest_non_multiple = Some(scores[i]);
            }
        }
        i = i + 1;
    }
    
    match smallest_non_multiple {
        None => {
            proof {
                assert(all_multiples_of_10(scores@.map(|j, x| x as int)));
            }
            0
        },
        Some(val) => {
            proof {
                assert(is_smallest_non_multiple(scores@.map(|j, x| x as int), val as int));
            }
            total_sum - val
        }
    }
}
// </vc-code>


}

fn main() {}