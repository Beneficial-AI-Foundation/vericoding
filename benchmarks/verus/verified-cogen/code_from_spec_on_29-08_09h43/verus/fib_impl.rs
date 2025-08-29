use vstd::prelude::*;

verus! {

spec fn fibo(n: int) -> (result:nat)
    decreases n
{
    if n <= 0 { 0 } else if n == 1 { 1 }
    else { fibo(n - 2) + fibo(n - 1) }
}
// pure-end
// pure-end

spec fn fibo_fits_i32(n: int) -> (result:bool) {
    fibo(n) < 0x8000_0000
}
// pure-end

// <vc-helpers>
proof fn fibo_is_monotonic(i: int, j: int)
    requires
        i <= j,
    ensures
        fibo(i) <= fibo(j),
    decreases j - i
{
    if i <= 0 {
    }
    else if  i < j {
        fibo_is_monotonic(i, j-1);
        assert(fibo(j) == fibo(j-1)+fibo(j-2));
    }
}

proof fn fibo_fits_implies_subseq_fits(n: int, k: int)
    requires
        fibo_fits_i32(n),
        k <= n,
    ensures
        fibo_fits_i32(k),
{
    fibo_is_monotonic(k, n);
}

proof fn fibo_base_cases()
    ensures
        fibo(0) == 0,
        fibo(1) == 1,
{
}

proof fn fibo_addition_safe(n: int)
    requires
        n >= 2,
        fibo_fits_i32(n),
    ensures
        fibo(n - 2) + fibo(n - 1) < 0x8000_0000,
{
    assert(fibo(n) == fibo(n - 2) + fibo(n - 1));
    assert(fibo(n) < 0x8000_0000);
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn fibonacci(n: usize) -> (ret: Vec<i32>)
    // pre-conditions-start
    requires
        fibo_fits_i32(n as int),
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] ==  fibo(i), 
        ret@.len() == n,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    result.push(0i32);
    result.push(1i32);
    
    proof {
        fibo_base_cases();
        assert(result@[0] == fibo(0));
        assert(result@[1] == fibo(1));
    }
    
    let mut i: usize = 2;
    /* code modified by LLM (iteration 3): added bounds checks and overflow safety proofs */
    while i < n
        invariant
            result@.len() == i,
            i >= 2,
            i <= n,
            fibo_fits_i32(n as int),
            forall |j: int| 0 <= j < i ==> #[trigger] result@[j] == fibo(j),
        decreases n - i
    {
        proof {
            fibo_fits_implies_subseq_fits(n as int, i as int);
            fibo_addition_safe(i as int);
        }
        
        /* code modified by LLM (iteration 3): ensure safe arithmetic by proving bounds */
        let val1 = result[(i - 2) as usize];
        let val2 = result[(i - 1) as usize];
        let fib_val = val1 + val2;
        result.push(fib_val);
        
        proof {
            assert(result@[i as int] == val1 + val2);
            assert(val1 == result@[i as int - 2]);
            assert(val2 == result@[i as int - 1]);
            assert(result@[i as int - 2] == fibo(i as int - 2));
            assert(result@[i as int - 1] == fibo(i as int - 1));
            assert(fibo(i as int) == fibo(i as int - 2) + fibo(i as int - 1));
            assert(result@[i as int] == fibo(i as int));
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}

fn main() {}