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
/* helper modified by LLM (iteration 5): Removed proof block from spec function and simplified */
proof fn lemma_min_seq_nonnegative_absolute(s: Seq<i8>) -> (min_abs: int)
    ensures
        min_abs == min_seq(Seq::new(s.len(), |i: int| if s[i] < 0 { -s[i] as int } else { s[i] as int })),
        min_abs >= 0,
{
    let abs_seq = Seq::new(s.len(), |i: int| if s[i] < 0 { -s[i] as int } else { s[i] as int });
    let min_abs = min_seq(abs_seq);
    
    if s.len() > 0 {
        assert(0 <= 0 < s.len());
        assert forall|i: int| 0 <= i < s.len() implies abs_seq[i] >= 0 by {
            if s[i] < 0 {
                assert(-s[i] as int >= 0);
            } else {
                assert(s[i] as int >= 0);
            }
        };
    }
    
    min_abs
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
    /* code modified by LLM (iteration 5): Fixed type conversions and proof obligations */
    let mut result: i8 = 0;
    let mut min_abs_val: i8 = i8::MAX;
    let mut count_neg = 0;
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            result as int == sum_seq(Seq::new(i as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int })),
            min_abs_val as int == min_seq(Seq::new(i as int, |j: int| if a@[j] < 0 { -a@[j] as int } else { a@[j] as int })) || i == 0,
            min_abs_val >= 0,
            count_neg == Set::new(|j: int| 0 <= j < i && a@[j] < 0).len(),
    {
        let val = a[i];
        let abs_val = if val < 0 { -val } else { val };
        
        if val < 0 {
            count_neg += 1;
        }
        
        if i == 0 || abs_val < min_abs_val {
            min_abs_val = abs_val;
        }
        
        result += abs_val;
        i += 1;
    }
    
    if count_neg % 2 == 1 {
        result -= 2 * min_abs_val;
    }
    
    result
}
// </vc-code>


}

fn main() {}