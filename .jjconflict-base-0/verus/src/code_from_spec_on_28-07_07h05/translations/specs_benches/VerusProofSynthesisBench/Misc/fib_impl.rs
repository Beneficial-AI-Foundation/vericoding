use vstd::prelude::*;

verus! {
spec fn fibo(n: int) -> (result:nat)
    decreases n
{
    if n <= 0 { 0 } else if n == 1 { 1 }
    else { fibo(n - 2) + fibo(n - 1) }
}
// pure-end

spec fn fibo_fits_i32(n: int) -> (result:bool) {
    fibo(n) < 0x8000_0000
}
// pure-end

proof fn fibo_is_monotonic(i: int, j: int)
    // pre-conditions-start
    requires
        i <= j,
    // pre-conditions-end
    // post-conditions-start
    ensures
        fibo(i) <= fibo(j),
    decreases j - i
    // post-conditions-end
{
    // impl-start
    if i <= 0 {
    }
    else if  i < j {
        fibo_is_monotonic(i, j-1);
        assert(fibo(j) == fibo(j-1)+fibo(j-2));
    }
    // impl-end
}
// pure-end

//IMPL fibonacci
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
{
    let mut result = Vec::new();
    result.push(0); // fibo(0) = 0
    result.push(1); // fibo(1) = 1
    
    /* code modified by LLM (iteration 1): added proof that fibo_fits_i32 holds for initial values */
    assert(fibo_fits_i32(0));
    assert(fibo_fits_i32(1));
    assert(fibo_fits_i32(2));
    
    let mut i = 2;
    while i < n
        invariant
            result@.len() == i,
            i >= 2,
            i <= n,
            forall |j: int| 0 <= j < i ==> result@[j] == fibo(j),
            /* code modified by LLM (iteration 1): fixed invariant range to match what we can prove */
            forall |j: int| 0 <= j < i ==> fibo_fits_i32(j),
            /* code modified by LLM (iteration 1): added invariant for current i value */
            fibo_fits_i32(i as int),
        decreases n - i,
    {
        let prev1 = result[i - 1];
        let prev2 = result[i - 2];
        
        /* code modified by LLM (iteration 1): added assertions to establish correctness of prev values */
        assert(result@[i - 1] == fibo((i - 1) as int));
        assert(result@[i - 2] == fibo((i - 2) as int));
        assert(prev1 == fibo((i - 1) as int));
        assert(prev2 == fibo((i - 2) as int));
        
        /* code modified by LLM (iteration 1): prove that addition won't overflow */
        assert(fibo(i as int) == fibo((i - 1) as int) + fibo((i - 2) as int));
        assert(fibo_fits_i32(i as int));
        assert(fibo(i as int) < 0x8000_0000);
        assert(prev1 as nat + prev2 as nat == fibo(i as int));
        /* code modified by LLM (iteration 2): fixed syntax error in assert statement */
        assert(prev1 as nat + prev2 as nat < 0x8000_0000);
        
        let next_fib = prev1 + prev2;
        
        /* code modified by LLM (iteration 1): prove the new element matches fibo(i) */
        assert(next_fib as nat == prev1 as nat + prev2 as nat);
        assert(next_fib == fibo(i as int));
        
        result.push(next_fib);
        
        /* code modified by LLM (iteration 1): prove invariants are maintained */
        assert(result@[i as int] == fibo(i as int));
        assert(forall |j: int| 0 <= j < i ==> result@[j] == fibo(j));
        
        /* code modified by LLM (iteration 1): prove fibo_fits_i32 for next iteration */
        if i + 1 < n {
            assert(fibo_fits_i32((i + 1) as int));
        }
        
        i += 1;
    }
    
    result
}
}

fn main() {}