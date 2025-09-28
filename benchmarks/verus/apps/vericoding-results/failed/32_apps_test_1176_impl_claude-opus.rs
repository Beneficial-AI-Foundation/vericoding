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
/* helper modified by LLM (iteration 2): Fixed syntax error in ensures clause */
proof fn sum_abs_lemma(a: &Vec<i8>, i: usize, sum: i32)
    requires
        0 <= i <= a@.len(),
        sum == sum_seq(Seq::new(i as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int }))
    ensures
        i < a@.len() ==> {
            let next_val = if a[i as usize] < 0 { -(a[i as usize] as i32) } else { a[i as usize] as i32 };
            sum + next_val == sum_seq(Seq::new((i + 1) as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int }))
        }
{
    if i < a@.len() {
        let s1 = Seq::new(i as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int });
        let s2 = Seq::new((i + 1) as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int });
        assert(s2.len() == (i + 1) as int);
        assert(s2[0] == (if a@[0] < 0 { -a@[0] as int } else { a@[0] as int }));
        assert(forall|j: int| 1 <= j < s2.len() ==> s2[j] == s1[j - 1]);
        assert(s2.subrange(1, s2.len() as int) =~= s1);
    }
}

proof fn min_abs_update_lemma(a: &Vec<i8>, i: usize, min_val: i32)
    requires
        0 <= i < a@.len(),
        i == 0 ==> min_val == i32::MAX,
        i > 0 ==> min_val == min_seq(Seq::new(i as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int }))
    ensures
        (if a[i as usize] < 0 { -(a[i as usize] as i32) } else { a[i as usize] as i32 }) < min_val ==>
            (if a[i as usize] < 0 { -(a[i as usize] as i32) } else { a[i as usize] as i32 }) == min_seq(Seq::new((i + 1) as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int })),
        (if a[i as usize] < 0 { -(a[i as usize] as i32) } else { a[i as usize] as i32 }) >= min_val ==>
            min_val == min_seq(Seq::new((i + 1) as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int }))
{
    let s = Seq::new((i + 1) as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int });
    if i == 0 {
        assert(s.len() == 1);
        assert(min_seq(s) == s[0]);
    } else {
        let s_prev = Seq::new(i as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int });
        assert(s.subrange(1, s.len() as int) =~= s_prev);
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
{
    /* code modified by LLM (iteration 2): Simplified min_abs tracking logic */
    let mut count_neg: usize = 0;
    let mut sum_abs: i32 = 0;
    let mut min_abs: i32 = i32::MAX;
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            count_neg == Set::new(|j: int| 0 <= j < i && a@[j] < 0).len(),
            sum_abs == sum_seq(Seq::new(i as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int })),
            i == 0 ==> min_abs == i32::MAX,
            i > 0 ==> min_abs == min_seq(Seq::new(i as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int }))
    {
        let val = a[i];
        let abs_val = if val < 0 { -(val as i32) } else { val as i32 };
        
        if val < 0 {
            count_neg = count_neg + 1;
        }
        
        proof {
            sum_abs_lemma(&a, i, sum_abs);
        }
        sum_abs = sum_abs + abs_val;
        
        let old_min = if i == 0 { i32::MAX } else { min_abs };
        min_abs = if abs_val < old_min { abs_val } else { old_min };
        
        proof {
            min_abs_update_lemma(&a, i, old_min);
        }
        
        i = i + 1;
    }

    assert(count_neg == Set::new(|j: int| 0 <= j < a@.len() && a@[j] < 0).len());
    assert(sum_abs == sum_seq(Seq::new(a@.len(), |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int })));
    assert(min_abs == min_seq(Seq::new(a@.len(), |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int })));

    if count_neg % 2 == 0 {
        sum_abs as i8
    } else {
        (sum_abs - 2 * min_abs) as i8
    }
}
// </vc-code>


}

fn main() {}