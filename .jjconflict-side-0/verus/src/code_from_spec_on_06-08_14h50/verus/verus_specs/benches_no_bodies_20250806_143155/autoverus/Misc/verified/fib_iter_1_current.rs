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
    if i <= 0 {
    }
    else if  i < j {
        fibo_is_monotonic(i, j-1);
        assert(fibo(j) == fibo(j-1)+fibo(j-2));
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
    result.push(0); // fibo(0) = 0
    result.push(1); // fibo(1) = 1
    
    let mut i = 2;
    while i < n
        invariant
            result@.len() == i,
            i >= 2,
            i <= n,
            forall |j: int| 2 <= j < i ==> result@[j] == fibo(j),
            result@[0] == 0,
            result@[1] == 1,
    {
        let prev1 = result[i - 1];
        let prev2 = result[i - 2];
        let next_fib = prev1 + prev2;
        
        proof {
            assert(result@[i - 1] == fibo((i - 1) as int));
            assert(result@[i - 2] == fibo((i - 2) as int));
            assert(fibo(i as int) == fibo((i - 2) as int) + fibo((i - 1) as int));
        }
        
        result.push(next_fib);
        i += 1;
    }
    
    result
}
}