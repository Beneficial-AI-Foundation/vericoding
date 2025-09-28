// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_ones_in_binary(n: int) -> int
    recommends n >= 1
    decreases n
    when n >= 1
{
    if n == 1 {
        1
    } else if n % 2 == 1 {
        1 + count_ones_in_binary(n / 2)
    } else {
        count_ones_in_binary(n / 2)
    }
}

spec fn valid_input(x: int) -> bool {
    x >= 1
}

spec fn valid_output(x: int, result: int) -> bool {
    valid_input(x) && result == count_ones_in_binary(x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma for bit count upper bound */
spec fn count_ones_extended(n: int) -> int
    recommends n >= 0
    decreases n
    when n >= 0
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else if n % 2 == 1 {
        1 + count_ones_extended(n / 2)
    } else {
        count_ones_extended(n / 2)
    }
}

proof fn lemma_count_ones_equivalence(n: int)
    requires n >= 1
    ensures count_ones_extended(n) == count_ones_in_binary(n)
    decreases n
{
    if n == 1 {
        assert(count_ones_extended(1) == 1);
        assert(count_ones_in_binary(1) == 1);
    } else if n % 2 == 1 {
        lemma_count_ones_equivalence(n / 2);
        assert(count_ones_extended(n) == 1 + count_ones_extended(n / 2));
        assert(count_ones_in_binary(n) == 1 + count_ones_in_binary(n / 2));
    } else {
        lemma_count_ones_equivalence(n / 2);
        assert(count_ones_extended(n) == count_ones_extended(n / 2));
        assert(count_ones_in_binary(n) == count_ones_in_binary(n / 2));
    }
}

proof fn lemma_count_ones_upper_bound(n: int)
    requires n >= 0
    ensures count_ones_extended(n) >= 0,
            count_ones_extended(n) <= n
    decreases n
{
    if n == 0 {
        assert(count_ones_extended(0) == 0);
    } else if n == 1 {
        assert(count_ones_extended(1) == 1);
    } else if n % 2 == 1 {
        lemma_count_ones_upper_bound(n / 2);
        assert(n / 2 < n);
        assert(count_ones_extended(n / 2) <= n / 2);
        assert(count_ones_extended(n) == 1 + count_ones_extended(n / 2));
        assert(count_ones_extended(n) <= 1 + n / 2);
        assert(1 + n / 2 <= n);
    } else {
        lemma_count_ones_upper_bound(n / 2);
        assert(count_ones_extended(n) == count_ones_extended(n / 2));
        assert(count_ones_extended(n) <= n / 2);
        assert(n / 2 < n);
    }
}
// </vc-helpers>

// <vc-spec>
fn min_bacteria(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures valid_output(x as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified proofs using upper bound lemma */
    let mut n: i8 = x;
    let mut count: i8 = 0;
    
    proof {
        lemma_count_ones_equivalence(x as int);
        lemma_count_ones_upper_bound(x as int);
    }
    
    while n > 0
        invariant
            n >= 0,
            n <= x,
            valid_input(x as int),
            count >= 0,
            count as int + count_ones_extended(n as int) == count_ones_extended(x as int),
            count_ones_extended(x as int) == count_ones_in_binary(x as int),
            count_ones_extended(x as int) <= x as int,
            count as int <= count_ones_extended(x as int),
        decreases n
    {
        proof {
            lemma_count_ones_upper_bound(n as int);
            assert(count_ones_extended(n as int) >= 0);
            assert(count_ones_extended(n as int) <= n as int);
            assert(count as int == count_ones_extended(x as int) - count_ones_extended(n as int));
        }
        
        if n % 2 == 1 {
            proof {
                assert(n > 0);
                assert(count_ones_extended(n as int) == 1 + count_ones_extended((n / 2) as int));
                assert(count as int + count_ones_extended(n as int) == count_ones_extended(x as int));
                assert(count as int < count_ones_extended(x as int));
                assert(count_ones_extended(x as int) <= x as int);
                assert(x as int <= i8::MAX as int);
                assert(count as int < i8::MAX as int);
            }
            count = count + 1;
        }
        
        proof {
            if n % 2 == 1 {
                assert(count_ones_extended(n as int) == 1 + count_ones_extended((n / 2) as int));
            } else {
                assert(count_ones_extended(n as int) == count_ones_extended((n / 2) as int));
            }
        }
        
        n = n / 2;
    }
    
    assert(n == 0);
    assert(count_ones_extended(0) == 0);
    assert(count as int == count_ones_extended(x as int));
    assert(count as int == count_ones_in_binary(x as int));
    
    count
}
// </vc-code>


}

fn main() {}