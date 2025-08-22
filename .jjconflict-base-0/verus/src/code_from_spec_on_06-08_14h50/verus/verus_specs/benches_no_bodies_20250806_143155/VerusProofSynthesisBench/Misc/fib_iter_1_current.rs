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
    result.push(0);  // fibo(0) = 0
    result.push(1);  // fibo(1) = 1
    
    let mut i = 2;
    while i < n
        invariant
            result@.len() == i,
            i >= 2,
            i <= n,
            forall |j: int| 0 <= j < i ==> result@[j] == fibo(j),
    {
        let next_fib = result[i - 2] + result[i - 1];
        result.push(next_fib);
        
        proof {
            assert(result@[i as int] == result@[(i-2) as int] + result@[(i-1) as int]);
            assert(result@[(i-2) as int] == fibo((i-2) as int));
            assert(result@[(i-1) as int] == fibo((i-1) as int));
            assert(fibo(i as int) == fibo((i-2) as int) + fibo((i-1) as int));
        }
        
        i += 1;
    }
    
    result
}
}

fn main() {}