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
    if i == j {
        // trivially true
    } else if j <= 0 {
        // fibo(i) = fibo(j) = 0
    } else if j == 1 {
        if i <= 0 {
            // fibo(i) = 0, fibo(j) = 1
        } else {
            // i = j = 1, already handled above
        }
    } else {
        // j >= 2, so fibo(j) = fibo(j-2) + fibo(j-1)
        if i <= j - 1 {
            fibo_is_monotonic(i, j - 1);
            // fibo(i) <= fibo(j-1) <= fibo(j-2) + fibo(j-1) = fibo(j)
        }
    }
}
// pure-end

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
    
    // Initialize with fibo(0) = 0 and fibo(1) = 1
    result.push(0);
    result.push(1);
    
    let mut i = 2;
    while i < n
        invariant
            result@.len() == i,
            i >= 2,
            i <= n,
            forall |j: int| 0 <= j < i ==> result@[j] == fibo(j),
        /* code modified by LLM (iteration 1): added decreases clause to show loop termination */
        decreases n - i
    {
        let fib_val = result[i - 2] + result[i - 1];
        result.push(fib_val);
        i += 1;
    }
    
    result
}
}

fn main() {}