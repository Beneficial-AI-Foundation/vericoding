// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min_spec(seq: Seq<i32>) -> (result: int)
    recommends
        0 < seq.len(),
    decreases seq.len(),
{
    if seq.len() == 1 {
        seq[0] as int
    } else if seq.len() == 0 {
        0
    } else {
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            seq[0] as int
        } else {
            later_min as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemma syntax by removing exclamation mark and adding proper function signature */
proof fn min_spec_lemma(seq: Seq<i32>, i: int) 
    requires 0 <= i < seq.len()
    ensures seq[i] as int >= min_spec(seq)
{
    if seq.len() == 1 {
        assert(seq[i] as int == min_spec(seq));
    } else {
        let later_min = min_spec(seq.drop_first());
        if i == 0 {
            if seq[0] <= later_min {
                assert(seq[0] as int == min_spec(seq));
            } else {
                assert(later_min as int == min_spec(seq));
            }
        } else {
            min_spec_lemma(seq.drop_first(), i - 1);
        }
    }
}

proof fn min_spec_non_empty(seq: Seq<i32>) 
    requires 0 < seq.len() 
    ensures exists|i: int| 0 <= i < seq.len() && seq[i] as int == min_spec(seq) 
{
    if seq.len() == 1 {
        assert(seq[0] as int == min_spec(seq));
    } else {
        min_spec_non_empty(seq.drop_first());
        let later_min = min_spec(seq.drop_first());
        if seq[0] <= later_min {
            assert(seq[0] as int == min_spec(seq));
        } else {
            assert(later_min as int == min_spec(seq));
        }
    }
}

proof fn min_spec_all_ge(seq: Seq<i32>, value: i32) 
    requires 0 < seq.len() 
    ensures value as int >= min_spec(seq) ==> forall|i: int| 0 <= i < seq.len() ==> value as int >= seq[i] as int 
{
    if value as int >= min_spec(seq) {
        forall|i: int| 0 <= i < seq.len() {
            min_spec_lemma(seq, i);
            assert(value as int >= seq[i] as int);
        }
    }
}

proof fn min_spec_drop_first(seq: Seq<i32>) 
    requires seq.len() > 1 
    ensures min_spec(seq) == min(seq[0] as int, min_spec(seq.drop_first())) 
{
    let later_min = min_spec(seq.drop_first());
    if seq[0] <= later_min {
        assert(min_spec(seq) == seq[0] as int);
        assert(min(seq[0] as int, later_min) == seq[0] as int);
    } else {
        assert(min_spec(seq) == later_min as int);
        assert(min(seq[0] as int, later_min) == later_min as int);
    }
}

fn min(a: int, b: int) -> int { if a < b { a } else { b } }

fn find_min_index(vec: &Vec<i32>, start: usize, end: usize) -> (index: usize)
    requires start <= end < vec.len()
    ensures index >= start && index <= end
    ensures forall|i: int| start <= i <= end ==> vec[index] as int <= vec[i] as int
    decreases end - start
{
    if start == end {
        start
    } else {
        let mid = (start + end) / 2;
        let left_min = find_min_index(vec, start, mid);
        let right_min = find_min_index(vec, mid + 1, end);
        if vec[left_min] <= vec[right_min] { left_min } else { right_min }
    }
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(numbers: &Vec<i32>) -> (indices: (usize, usize))

    requires
        numbers.len() >= 2,

    ensures
        forall|k: int|
            0 <= k < numbers.len() && k != indices.0 && numbers[indices.0 as int] == min_spec(
                numbers@,
            ) ==> (#[trigger] numbers[k] >= numbers[indices.1 as int]),
        exists|k: int|
            0 <= k < numbers.len() && k != indices.0 && (#[trigger] numbers[k]
                == numbers[indices.1 as int]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation by using proof function syntax */
{
    let min_index = find_min_index(numbers, 0, numbers.len() - 1);
    proof {
        min_spec_non_empty(numbers@);
        min_spec_lemma(numbers@, min_index as int);
    }
    
    let second_min_index = if min_index == 0 { 1 } else { 0 };
    let mut candidate = second_min_index;
    let mut i: usize = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            candidate != min_index,
            numbers[candidate] as int >= min_spec(numbers@),
            exists|j: int| 0 <= j < i && j != min_index as int && numbers[j] as int == numbers[candidate] as int,
        decreases numbers.len() - i,
    {
        if i != min_index && (i == candidate || numbers[i] < numbers[candidate]) {
            candidate = i;
        }
        i += 1;
    }
    
    proof {
        min_spec_all_ge(numbers@, numbers[candidate]);
    }
    
    (min_index, candidate)
}
// </vc-code>

}
fn main() {}