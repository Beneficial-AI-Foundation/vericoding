// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}

spec fn min_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0
    } else if s.len() == 1 { 
        s[0] 
    } else { 
        let rest_min = min_seq(s.subrange(1, s.len() as int));
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}
// </vc-preamble>

// <vc-helpers>
fn count_negatives(a: &Vec<i8>) -> (count: usize)
    ensures
        count as int == Set::new(|i: int| 0 <= i < a@.len() && a@[i] < 0).len(),
{
    let mut c: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            c as int == Set::new(|j: int| 0 <= j < i && a@[j] < 0).len(),
        decreases a.len() - i
    {
        if a[i] < 0 {
            c += 1;
        }
        i += 1;
    }
    c
}

fn sum_abs(a: &Vec<i8>) -> (sum: i64)
    ensures
        sum as int == sum_seq(Seq::new(a@.len(), |i: int| if a@[i] < 0 { -a@[i] as int } else { a@[i] as int })),
{
    let mut s: i64 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            s as int == sum_seq(Seq::new(i, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int })),
        decreases a.len() - i
    {
        let abs_val_int: int = if a[i] < 0 { -(a[i] as int) } else { a[i] as int };
        let abs_val: i64 = abs_val_int as i64;
        s = s + abs_val;
        i += 1;
    }
    s
}

/* helper modified by LLM (iteration 5): Fixed type mismatches by using nat for Seq lengths and separate int/i64 for abs values */
fn min_abs(a: &Vec<i8>) -> (min: i64)
    ensures
        min as int == min_seq(Seq::new(a@.len(), |i: int| if a@[i] < 0 { -a@[i] as int } else { a@[i] as int })),
        min >= 0,
{
    let len = a.len();
    if len == 1 {
        if a[0] < 0 {
            -(a[0] as i64)
        } else {
            a[0] as i64
        }
    } else {
        let mut min_val: i64 = if a[0] < 0 { -(a[0] as i64) } else { a[0] as i64 };
        let mut i: usize = 1;
        while i < a.len()
            invariant
                1 <= i <= a@.len(),
                min_val as int == min_seq(Seq::new(i, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int })),
                min_val >= 0,
            decreases a.len() - i
        {
            let abs_val_int: int = if a[i] < 0 { -(a[i] as int) } else { a[i] as int };
            let abs_val: i64 = abs_val_int as i64;
            if abs_val < min_val {
                min_val = abs_val;
            }
            proof {
                let prev_seq = Seq::new(i, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int });
                let new_seq = Seq::new(i + 1, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int });
                assert(new_seq == prev_seq.push(abs_val_int));
                assert(min_seq(new_seq) == if abs_val_int < min_seq(prev_seq) { abs_val_int } else { min_seq(prev_seq) });
            }
            i += 1;
        }
        min_val
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: i8)
    requires a@.len() >= 2
    ensures ({
        let count_neg = Set::new(|i: int| 0 <= i < a@.len() && a@[i] < 0).len();
        let sum_abs = sum_seq(Seq::new(a@.len(), |i: int| if a@[i] < 0 { -a@[i] as int } else { a@[i] as int }));
        let min_abs = min_seq(Seq::new(a@.len(), |i: int| if a@[i] < 0 { -a@[i] as int } else { a@[i] as int }));
        result as int == if count_neg % 2 == 0 { sum_abs } else { sum_abs - 2 * min_abs }
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implemented the logic using helper functions */
{
    let count_neg = count_negatives(&a);
    let sum_abs = sum_abs(&a);
    let min_abs = min_abs(&a);
    let res = if count_neg % 2 == 0 { sum_abs } else { sum_abs - 2 * min_abs };
    res as i8
}
// </vc-code>


}

fn main() {}