// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_valid_minutes(a: int, b: int) -> int
    recommends a >= 0 && b >= 0
    decreases a + b
{
    if a <= 0 || b <= 0 {
        0
    } else if a == 1 && b == 1 {
        0
    } else {
        (if a > 1 || b > 1 { 1 as int } else { 0 as int }) + 
        count_valid_minutes(
            if a < b { a + 1 } else { a - 2 }, 
            if a < b { b - 2 } else { b + 1 }
        )
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_count_valid_minutes_decreases(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures a + b >= 0
{
}

proof fn lemma_count_valid_minutes_positive_case(a: int, b: int)
    requires a >= 1, b >= 1, a != 1 || b != 1
    ensures count_valid_minutes(a, b) == 1 + count_valid_minutes(
        if a < b { a + 1 } else { a - 2 },
        if a < b { b - 2 } else { b + 1 }
    )
{
}

/* helper modified by LLM (iteration 5): Fixed cast safety to use i16 values */
proof fn lemma_i16_addition_safe(a: i16, b: i16) 
    requires a >= 0, b <= i8::MAX as i16
    ensures a + b >= 0
{
}

proof fn lemma_i8_cast_safe(val: i16) 
    requires val >= 0, val <= i8::MAX as i16
    ensures val as i8 >= 0
{
}

proof fn lemma_cast_i8_to_i16_safe(val: i8)
    requires val >= 0
    ensures val as i16 >= 0
{
}


// </vc-helpers>

// <vc-spec>
fn solve(a1: i8, a2: i8) -> (result: i8)
    requires 
        a1 >= 1 && a2 >= 1,
    ensures 
        result >= 0,
        result as int == count_valid_minutes(a1 as int, a2 as int),
        (a1 == 1 && a2 == 1) ==> result == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatch in lemma call */
    if a1 == 1 && a2 == 1 {
        return 0;
    }
    
    let mut m1 = a1 as i16;
    let mut m2 = a2 as i16;
    let mut count: i8 = 0;
    
    while m1 > 0 && m2 > 0
        invariant
            m1 >= 0, m2 >= 0,
            count >= 0,
            count as int == count_valid_minutes(m1 as int, m2 as int)
        decreases m1 as nat + m2 as nat
    {
        if m1 == 1 && m2 == 1 {
            break;
        }
        
        let old_m1 = m1;
        let old_m2 = m2;
        
        proof { lemma_count_valid_minutes_positive_case(old_m1 as int, old_m2 as int); }
        
        if m1 < m2 {
            proof { lemma_i16_addition_safe(m1, 1); }
            m1 += 1;
            m2 -= 2;
        } else {
            proof { lemma_i16_addition_safe(m2, 1); }
            m1 -= 2;
            m2 += 1;
        }
        
        let count_i16: i16 = count as i16;
        let new_count_i16 = count_i16 + 1;
        
        proof { 
            lemma_i16_addition_safe(count_i16, 1);
            lemma_i8_cast_safe(new_count_i16);
        }
        count = new_count_i16 as i8;
        
        proof { lemma_count_valid_minutes_decreases(m1 as int, m2 as int); }
    }
    
    count
}
// </vc-code>


}

fn main() {}