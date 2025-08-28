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
    else if i < j {
        fibo_is_monotonic(i, j-1);
        assert(fibo(j) == fibo(j-1) + fibo(j-2));
    }
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
fn fibonacci(n: usize) -> (ret: Vec<i32>)
    requires
        fibo_fits_i32(n as int),
        n >= 2,
    ensures
        forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] == fibo(i),
        ret@.len() == n,
{
    let mut v: Vec<i32> = Vec::with_capacity(n);
    v.push(0);
    v.push(1);
    let mut i: usize = 2;
    while i < n
        invariant
            v@.len() == i,
            i <= n,
            forall |j: int| 0 <= j < i ==> #[trigger] v@[j] == fibo(j),
    {
        let next_val = v@[(i - 1) as int] + v@[(i - 2) as int];
        v.push(next_val);
        i = i + 1;
    }
    v
}
// </vc-code>

}

fn main() {}