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
    while i < n
        invariant
            result@.len() == i,
            i >= 2,
            i <= n,
            forall |j: int| 0 <= j < i && j >= 2 ==> result@[j] == fibo(j),
            result@[0] == 0,
            result@[1] == 1,
    {
        let fib_prev2 = result[i - 2];
        let fib_prev1 = result[i - 1];
        let next_fib = fib_prev2 + fib_prev1;
        
        result.push(next_fib);
        i += 1;
    }
    
    result
}
}