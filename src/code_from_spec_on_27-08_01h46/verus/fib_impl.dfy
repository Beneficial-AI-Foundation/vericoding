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

proof fn fibo_fits_propagates(n: int)
    requires
        fibo_fits_i32(n as int),
        n >= 2,
    ensures
        fibo_fits_i32(n - 1),
        fibo_fits_i32(n - 2),
        fibo(n - 1) < 0x8000_0000,
        fibo(n - 2) < 0x8000_0000,
{
    fibo_is_monotonic(n - 2, n);
    fibo_is_monotonic(n - 1, n);
}

proof fn fibo_addition_safe(i: int, n: int)
    requires
        fibo_fits_i32(n),
        2 <= i < n,
    ensures
        fibo(i - 2) + fibo(i - 1) < 0x8000_0000,
{
    fibo_is_monotonic(i, n);
    assert(fibo(i) == fibo(i - 2) + fibo(i - 1));
    assert(fibo(i) <= fibo(n));
    assert(fibo(n) < 0x8000_0000);
}
// </vc-helpers>

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
    result.push(0);
    result.push(1);
    
    let mut i: usize = 2;
    while i < n
        invariant
            result@.len() == i,
            i >= 2,
            i <= n,
            forall |j: int| #![auto] 0 <= j < i ==> result@[j] == fibo(j),
            fibo_fits_i32(n as int),
        decreases n - i
    {
        proof {
            fibo_addition_safe(i as int, n as int);
            assert(result@[i as int - 2] == fibo(i as int - 2));
            assert(result@[i as int - 1] == fibo(i as int - 1));
            assert(fibo(i as int) == fibo(i as int - 2) + fibo(i as int - 1));
        }
        
        let fib_val = result[i - 2] + result[i - 1];
        result.push(fib_val);
        
        proof {
            assert(result@[i as int] == fib_val);
            assert(fib_val == fibo(i as int));
            assert(forall |j: int| 0 <= j < i ==> result@[j] == fibo(j));
            assert(forall |j: int| 0 <= j < i + 1 ==> result@[j] == fibo(j));
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}

fn main() {}