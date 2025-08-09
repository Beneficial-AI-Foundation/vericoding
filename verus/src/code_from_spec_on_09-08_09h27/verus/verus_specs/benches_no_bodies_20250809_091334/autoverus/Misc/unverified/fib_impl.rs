use vstd::prelude::*;
fn main() {}

verus! {
spec fn fibo(n: int) -> nat
    decreases n
{
    if n <= 0 { 0 } else if n == 1 { 1 }
    else { fibo(n - 2) + fibo(n - 1) }
}

spec fn fibo_fits_i32(n: int) -> bool {
    fibo(n) < 0x8000_0000
}

fn fibonacci(n: usize) -> (ret: Vec<i32>)
requires
    fibo_fits_i32(n as int),
    n >= 2,
ensures
    forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] ==  fibo(i), 
    ret@.len() == n,
{
    let mut result = Vec::new();
    
    // Initialize first two Fibonacci numbers
    result.push(0); // fibo(0) = 0
    result.push(1); // fibo(1) = 1
    
    // Generate remaining Fibonacci numbers
    let mut i = 2;
    /* code modified by LLM (iteration 1): added decreases clause and fixed invariants */
    while i < n
        invariant
            result@.len() == i,
            i >= 2,
            i <= n,
            forall |j: int| 0 <= j < i && j >= 2 ==> result@[j] == fibo(j),
            result@[0] == 0,
            result@[1] == 1,
        decreases n - i
    {
        /* code modified by LLM (iteration 1): added proof block and bounds check */
        let fib_prev2 = result[i - 2];
        let fib_prev1 = result[i - 1];
        
        proof {
            assert(i >= 2);
            assert(i - 2 >= 0);
            assert(i - 1 >= 0);
            assert(i - 2 < result@.len());
            assert(i - 1 < result@.len());
            
            // Prove the values we're accessing are correct
            if i - 2 >= 2 {
                assert(result@[i - 2] == fibo((i - 2) as int));
            } else {
                assert(i - 2 == 0);
                assert(result@[i - 2] == 0);
                assert(fibo((i - 2) as int) == 0);
            }
            
            if i - 1 >= 2 {
                assert(result@[i - 1] == fibo((i - 1) as int));
            } else {
                assert(i - 1 == 1);
                assert(result@[i - 1] == 1);
                assert(fibo((i - 1) as int) == 1);
            }
        }
        
        let next_fib = fib_prev2 + fib_prev1;
        
        proof {
            // Prove that next_fib equals fibo(i)
            assert(next_fib == fib_prev2 + fib_prev1);
            assert(fib_prev2 == result@[(i - 2) as int]);
            assert(fib_prev1 == result@[(i - 1) as int]);
            
            if i - 2 >= 2 {
                assert(fib_prev2 == fibo((i - 2) as int));
            } else {
                assert(fib_prev2 == 0);
                assert(fibo((i - 2) as int) == 0);
            }
            
            if i - 1 >= 2 {
                assert(fib_prev1 == fibo((i - 1) as int));
            } else {
                assert(fib_prev1 == 1);
                assert(fibo((i - 1) as int) == 1);
            }
            
            assert(next_fib == fibo((i - 2) as int) + fibo((i - 1) as int));
            assert(fibo(i as int) == fibo((i - 2) as int) + fibo((i - 1) as int));
            assert(next_fib == fibo(i as int));
        }
        
        result.push(next_fib);
        i += 1;
    }
    
    result
}
}