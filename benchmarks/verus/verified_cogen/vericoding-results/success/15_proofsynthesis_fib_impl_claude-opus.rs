// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fibo(n: int) -> (result:nat)
    decreases n
{
    if n <= 0 { 0 } else if n == 1 { 1 }
    else { fibo(n - 2) + fibo(n - 1) }
}

spec fn fibo_fits_i32(n: int) -> (result:bool) {
    fibo(n) < 0x8000_0000
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_fibo_monotonic(n: int)
    requires n >= 0
    ensures fibo(n) <= fibo(n + 1)
    decreases n
{
    if n == 0 {
        assert(fibo(0) == 0);
        assert(fibo(1) == 1);
    } else if n == 1 {
        assert(fibo(1) == 1);
        assert(fibo(2) == fibo(0) + fibo(1) == 0 + 1 == 1);
    } else {
        lemma_fibo_monotonic(n - 1);
        assert(fibo(n - 1) <= fibo(n));
    }
}

proof fn lemma_fibo_bounded(n: int, m: int)
    requires 
        n >= 0,
        m >= n,
        fibo_fits_i32(m),
    ensures
        fibo(n) < 0x8000_0000
    decreases m - n
{
    if n == m {
        assert(fibo_fits_i32(m));
        assert(fibo(n) < 0x8000_0000);
    } else {
        lemma_fibo_bounded(n, m - 1);
        lemma_fibo_monotonic(n);
        assert(fibo(n) <= fibo(n + 1));
        if n < m - 1 {
            lemma_fibo_bounded(n + 1, m - 1);
            assert(fibo(n + 1) < 0x8000_0000);
        }
        assert(fibo(n) < 0x8000_0000);
    }
}
// </vc-helpers>

// <vc-spec>
fn fibonacci(n: usize) -> (ret: Vec<i32>)

    requires
        fibo_fits_i32(n as int),
        n >= 2,

    ensures
        forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] ==  fibo(i), 
        ret@.len() == n,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed lemma calls and assertions */
    let mut v = Vec::new();
    v.push(0i32);
    v.push(1i32);
    
    proof {
        assert(fibo(0) == 0);
        assert(fibo(1) == 1);
        lemma_fibo_bounded(2, n as int);
    }
    
    let mut i: usize = 2;
    while i < n
        invariant
            2 <= i <= n,
            v@.len() == i,
            forall |j: int| 0 <= j < i ==> v@[j] == fibo(j),
            fibo_fits_i32(n as int),
            i >= 2 ==> v@[i-1] == fibo((i-1) as int),
            i >= 2 ==> v@[i-2] == fibo((i-2) as int),
        decreases n - i
    {
        let prev1 = v[i - 1];
        let prev2 = v[i - 2];
        
        proof {
            lemma_fibo_bounded(i as int, n as int);
            assert(prev1 == fibo((i-1) as int));
            assert(prev2 == fibo((i-2) as int));
            assert(fibo(i as int) == fibo((i-2) as int) + fibo((i-1) as int));
            assert(fibo(i as int) < 0x8000_0000);
        }
        
        let next = prev2 + prev1;
        v.push(next);
        
        proof {
            assert(v@[i as int] == next);
            assert(next == prev2 + prev1);
            assert(next == fibo((i-2) as int) + fibo((i-1) as int));
            assert(next == fibo(i as int));
            assert(forall |j: int| 0 <= j < i + 1 ==> v@[j] == fibo(j));
        }
        
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}