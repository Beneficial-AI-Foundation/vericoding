use vstd::prelude::*;

verus! {

// <vc-helpers>
fn max_negative(lst: &Vec<i32>) -> Option<i32>
    ensures match result {
        Some(max_neg) => {
            max_neg < 0 && 
            (exists|i: int| 0 <= i < lst@.len() && lst@[i] == max_neg) &&
            (forall|i: int| 0 <= i < lst@.len() && lst@[i] < 0 ==> lst@[i] <= max_neg)
        },
        None => forall|i: int| 0 <= i < lst@.len() ==> lst@[i] >= 0
    }
{
    let mut max_neg: Option<i32> = None;
    let mut idx = 0;
    
    while idx < lst.len()
        invariant
            0 <= idx <= lst@.len(),
            match max_neg {
                Some(mn) => {
                    mn < 0 &&
                    (exists|i: int| 0 <= i < idx && lst@[i] == mn) &&
                    (forall|i: int| 0 <= i < idx && lst@[i] < 0 ==> lst@[i] <= mn)
                },
                None => forall|i: int| 0 <= i < idx ==> lst@[i] >= 0
            }
    {
        let val = lst[idx];
        if val < 0 {
            match max_neg {
                Some(current_max) => {
                    if val > current_max {
                        max_neg = Some(val);
                    }
                }
                None => {
                    max_neg = Some(val);
                }
            }
        }
        idx += 1;
    }
    
    max_neg
}

fn min_positive(lst: &Vec<i32>) -> Option<i32>
    ensures match result {
        Some(min_pos) => {
            min_pos > 0 && 
            (exists|i: int| 0 <= i < lst@.len() && lst@[i] == min_pos) &&
            (forall|i: int| 0 <= i < lst@.len() && lst@[i] > 0 ==> lst@[i] >= min_pos)
        },
        None => forall|i: int| 0 <= i < lst@.len() ==> lst@[i] <= 0
    }
{
    let mut min_pos: Option<i32> = None;
    let mut idx = 0;
    
    while idx < lst.len()
        invariant
            0 <= idx <= lst@.len(),
            match min_pos {
                Some(mp) => {
                    mp > 0 &&
                    (exists|i: int| 0 <= i < idx && lst@[i] == mp) &&
                    (forall|i: int| 0 <= i < idx && lst@[i] > 0 ==> lst@[i] >= mp)
                },
                None => forall|i: int| 0 <= i < idx ==> lst@[i] <= 0
            }
    {
        let val = lst[idx];
        if val > 0 {
            match min_pos {
                Some(current_min) => {
                    if val < current_min {
                        min_pos = Some(val);
                    }
                }
                None => {
                    min_pos = Some(val);
                }
            }
        }
        idx += 1;
    }
    
    min_pos
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def largest_smallest_integers(lst: List[int]) -> Tuple[ Optional[Int], Optional[Int] ]"
docstring: |
Create a function that returns a tuple (a, b), where 'a' is
the largest of negative integers, and 'b' is the smallest
of positive integers in a list.
If there is no negative or positive integers, return them as None.
test_cases:
- input: [2, 4, 1, 3, 5, 7]
expected_output: (None, 1)
- input: []
expected_output: (None, None)
- input: [0]
expected_output: (None, None)
*/
// </vc-description>

// <vc-spec>
fn largest_smallest_integers(lst: &Vec<i32>) -> (Option<i32>, Option<i32>)
    requires true
    ensures match result.0 {
        Some(max_neg) => {
            max_neg < 0 && 
            (exists|i: int| 0 <= i < lst@.len() && lst@[i] == max_neg) &&
            (forall|i: int| 0 <= i < lst@.len() && lst@[i] < 0 ==> lst@[i] <= max_neg)
        },
        None => forall|i: int| 0 <= i < lst@.len() ==> lst@[i] >= 0
    }
    ensures match result.1 {
        Some(min_pos) => {
            min_pos > 0 && 
            (exists|i: int| 0 <= i < lst@.len() && lst@[i] == min_pos) &&
            (forall|i: int| 0 <= i < lst@.len() && lst@[i] > 0 ==> lst@[i] >= min_pos)
        },
        None => forall|i: int| 0 <= i < lst@.len() ==> lst@[i] <= 0
    }
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): call helper functions */
    let max_neg = max_negative(lst);
    let min_pos = min_positive(lst);
    (max_neg, min_pos)
}
// </vc-code>

}
fn main() {}