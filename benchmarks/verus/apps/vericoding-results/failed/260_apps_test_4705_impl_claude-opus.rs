// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    1 <= n <= 100
}

spec fn total_cost(n: int) -> int
    recommends valid_input(n)
{
    800 * n
}

spec fn cashback(n: int) -> int
    recommends valid_input(n)
{
    (n / 15) * 200
}

spec fn net_amount(n: int) -> int
    recommends valid_input(n)
{
    total_cost(n) - cashback(n)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == net_amount(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use i32 for intermediate calculations to avoid overflow */
    let n_32: i32 = n as i32;
    
    proof {
        assert(1 <= n as int <= 100);
        assert(n_32 as int == n as int);
        assert(800 * n as int <= 800 * 100);
        assert(800 * n as int <= 80000);
    }
    
    let total: i32 = 800i32 * n_32;
    
    proof {
        assert(total as int == 800 * n as int);
        assert(total as int == total_cost(n as int));
    }
    
    let cashback_amount: i32 = (n_32 / 15i32) * 200i32;
    
    proof {
        assert(cashback_amount as int == (n as int / 15) * 200);
        assert(cashback_amount as int == cashback(n as int));
        assert(cashback_amount as int >= 0);
        assert(cashback_amount as int <= (100 / 15) * 200);
        assert(cashback_amount as int <= 1200);
    }
    
    let result_32: i32 = total - cashback_amount;
    
    proof {
        assert(result_32 as int == total as int - cashback_amount as int);
        assert(result_32 as int == total_cost(n as int) - cashback(n as int));
        assert(result_32 as int == net_amount(n as int));
        assert(result_32 as int >= 800 - 1200);
        assert(result_32 as int <= 80000);
        assert(-128 <= result_32 as int <= 127) by {
            assert(result_32 as int >= 800 * 1 - ((100/15) * 200));
            assert(result_32 as int >= 800 - 1200);
            assert(result_32 as int >= -400);
            assert(result_32 as int <= 800 * 100);
            assert(result_32 as int <= 80000);
        }
    }
    
    let result: i8 = result_32 as i8;
    
    proof {
        assert(result as int == result_32 as int);
        assert(result as int == net_amount(n as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}