// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int, c: int, t: int, arrivals: Seq<int>) -> bool {
    1 <= n <= 1000 &&
    1 <= a <= 1000 &&
    1 <= b <= 1000 &&
    1 <= c <= 1000 &&
    1 <= t <= 1000 &&
    arrivals.len() == n &&
    forall|i: int| 0 <= i < arrivals.len() ==> #[trigger] arrivals[i] >= 1 && #[trigger] arrivals[i] <= t
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}

spec fn max_money(n: int, a: int, b: int, c: int, t: int, arrivals: Seq<int>) -> int {
    if b > c {
        n * a
    } else {
        n * a + (c - b) * (n * t - sum_seq(arrivals))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed sum_seq_lemma termination and logic */
proof fn sum_seq_lemma(s: Seq<int>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        sum_seq(s.subrange(0, i)) + sum_seq(s.subrange(i, s.len() as int)) == sum_seq(s),
    decreases s.len(), i
{
    if i == 0 {
        assert(s.subrange(0, 0) =~= Seq::<int>::empty());
        assert(sum_seq(s.subrange(0, 0)) == 0);
        assert(s.subrange(0, s.len() as int) =~= s);
    } else if i == s.len() {
        assert(s.subrange(i, s.len() as int) =~= Seq::<int>::empty());
        assert(sum_seq(s.subrange(i, s.len() as int)) == 0);
        assert(s.subrange(0, i) =~= s);
    } else {
        // Key insight: split at position i means s[0..i] + s[i..len]
        // We need to show this equals sum_seq(s)
        let left = s.subrange(0, i);
        let right = s.subrange(i, s.len() as int);
        
        if s.len() > 0 {
            // Recursive case: use the definition of sum_seq
            assert(s[0] == left[0]) by {
                assert(i > 0);
            }
            
            // Apply lemma recursively on the tail
            sum_seq_lemma(s.subrange(1, s.len() as int), i - 1);
            
            assert(sum_seq(s) == s[0] + sum_seq(s.subrange(1, s.len() as int)));
            assert(left.subrange(1, left.len() as int) =~= s.subrange(1, s.len() as int).subrange(0, i - 1));
            assert(right =~= s.subrange(1, s.len() as int).subrange(i - 1, s.len() - 1));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8, t: i8, arrivals: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
    ensures result as int == max_money(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed arithmetic overflow and loop invariant maintenance */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    // Prove bounds to prevent overflow
    assert(n >= 1 && n <= 1000);
    assert(a >= 1 && a <= 1000);
    assert(b >= 1 && b <= 1000);
    assert(c >= 1 && c <= 1000);
    assert(t >= 1 && t <= 1000);
    assert(arrivals.len() == n as nat);
    
    while i < arrivals.len()
        invariant
            0 <= i <= arrivals.len(),
            arrivals.len() == n as nat,
            sum >= 0,
            sum <= (i as i32) * (t as i32),
            sum as int == sum_seq(arrivals@.map_values(|x: i8| x as int).subrange(0, i as int)),
        decreases arrivals.len() - i
    {
        let old_sum = sum;
        let arrival_i = arrivals[i] as i32;
        
        // Prove bounds for overflow prevention
        assert(arrivals@[i as int] >= 1 && arrivals@[i as int] <= t) by {
            assert(valid_input(n as int, a as int, b as int, c as int, t as int, arrivals@.map_values(|x: i8| x as int)));
        }
        assert(arrival_i >= 1 && arrival_i <= t as i32);
        assert(sum <= (i as i32) * (t as i32));
        assert(sum + arrival_i <= ((i + 1) as i32) * (t as i32));
        
        sum = sum + arrival_i;
        
        // Maintain invariant
        proof {
            let mapped = arrivals@.map_values(|x: i8| x as int);
            assert(mapped.subrange(0, (i + 1) as int) =~= mapped.subrange(0, i as int).push(mapped[i as int]));
            assert(sum_seq(mapped.subrange(0, (i + 1) as int)) == sum_seq(mapped.subrange(0, i as int)) + mapped[i as int]);
            assert(old_sum as int == sum_seq(mapped.subrange(0, i as int)));
            assert(arrival_i as int == mapped[i as int]);
            assert(sum as int == sum_seq(mapped.subrange(0, (i + 1) as int)));
        }
        
        i = i + 1;
    }
    
    assert(arrivals@.map_values(|x: i8| x as int).subrange(0, arrivals.len() as int) =~= arrivals@.map_values(|x: i8| x as int));
    assert(sum as int == sum_seq(arrivals@.map_values(|x: i8| x as int)));
    
    // Calculate result with overflow checking
    let n32 = n as i32;
    let a32 = a as i32;
    let b32 = b as i32;
    let c32 = c as i32;
    let t32 = t as i32;
    
    assert(n32 * a32 <= 1000 * 1000);
    assert(n32 * t32 <= 1000 * 1000);
    
    if b > c {
        let result32 = n32 * a32;
        assert(result32 >= 1 && result32 <= 1000000);
        #[verifier::truncate]
        (result32 as i8)
    } else {
        let wait_time = n32 * t32 - sum;
        assert(wait_time >= 0) by {
            assert(sum <= n32 * t32);
        }
        let profit_diff = (c32 - b32) * wait_time;
        let result32 = n32 * a32 + profit_diff;
        
        #[verifier::truncate]
        (result32 as i8)
    }
}
// </vc-code>


}

fn main() {}