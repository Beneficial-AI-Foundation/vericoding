#[allow(unused_imports)]
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

proof fn fibo_is_monotonic(i: int, j: int)
    requires
        i <= j,
    ensures
        fibo(i) <= fibo(j),
    decreases j - i
{
    if i == j {
        // Base case: fibo(i) == fibo(j)
    } else if j <= 0 {
        // Both fibo(i) and fibo(j) are 0
    } else if i <= 0 {
        // fibo(i) = 0, fibo(j) >= 0
    } else if j == 1 {
        // i <= 1, so either fibo(i) = 0 or fibo(i) = 1
    } else {
        // j >= 2, so fibo(j) = fibo(j-2) + fibo(j-1)
        if i >= j - 1 {
            // i is either j-1 or j, already handled above or i == j
            if i == j - 1 {
                // fibo(j-1) <= fibo(j-2) + fibo(j-1) = fibo(j)
            }
        } else {
            // i < j - 1, so i <= j - 2
            fibo_is_monotonic(i, j - 1);
            fibo_is_monotonic(j - 2, j - 1);
            // fibo(i) <= fibo(j-1) <= fibo(j-2) + fibo(j-1) = fibo(j)
        }
    }
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
    
    // Initialize first two values
    result.push(0); // fibo(0) = 0
    result.push(1); // fibo(1) = 1
    
    // Compute remaining Fibonacci numbers
    let mut k = 2;
    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while k < n
        invariant
            result@.len() == k,
            k >= 2,
            k <= n,
            forall |i: int| 0 <= i < k ==> result@[i] == fibo(i),
        decreases n - k
    {
        let next_fib = result[k - 2] + result[k - 1];
        result.push(next_fib);
        k += 1;
    }
    
    result
}
}