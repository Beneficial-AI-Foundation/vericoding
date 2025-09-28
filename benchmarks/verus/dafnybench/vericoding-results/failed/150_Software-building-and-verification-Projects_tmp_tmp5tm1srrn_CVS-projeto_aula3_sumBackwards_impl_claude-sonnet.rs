use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat 
    decreases n
{
    if n == 0 { 
        1 
    } else if n == 1 { 
        1 
    } else { 
        fib((n-1) as nat) + fib((n-2) as nat)
    }
}


// 2.
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>)
}

spec fn add(l: List<int>) -> int 
    decreases l
{
    match l {
        List::Nil => 0,
        List::Cons(x, xs) => x + add(*xs)
    }
}


// 3.

// 5.

// 6
spec fn sum(n: nat) -> nat 
    decreases n
{
    if n == 0 { 
        0 
    } else { 
        n + sum((n-1) as nat)
    }
}

// <vc-helpers>
spec fn sum_iter(i: nat, n: nat) -> nat 
    decreases (if i <= n { n + 1 - i } else { 0 })
{
    if i > n {
        0
    } else {
        i + sum_iter(i + 1, n)
    }
}

proof fn sum_iter_shift(n: nat)
    requires n >= 1
    ensures sum_iter(2, n) == sum_iter(1, (n - 1) as nat) + n
    decreases n
{
    if n == 1 {
        assert(sum_iter(2, 1) == 0);
        assert(sum_iter(1, 0) == 0);
    } else {
        sum_iter_shift((n - 1) as nat);
        assert(sum_iter(2, n) == 2 + sum_iter(3, n));
        assert(sum_iter(3, n) == sum_iter(2, (n - 1) as nat) + n);
        assert(sum_iter(2, (n - 1) as nat) == sum_iter(1, (n - 2) as nat) + (n - 1));
        assert(sum_iter(1, (n - 1) as nat) == 1 + sum_iter(2, (n - 1) as nat));
    }
}

proof fn sum_iter_equiv(n: nat)
    ensures sum_iter(1, n) == sum(n)
    decreases n
{
    if n == 0 {
        assert(sum_iter(1, 0) == 0);
        assert(sum(0) == 0);
    } else {
        sum_iter_equiv((n - 1) as nat);
        assert(sum_iter(1, n) == 1 + sum_iter(2, n));
        
        sum_iter_shift(n);
        assert(sum_iter(1, (n - 1) as nat) == sum((n - 1) as nat));
        assert(sum_iter(1, n) == 1 + sum((n - 1) as nat) + n);
        assert(sum(n) == n + sum((n - 1) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    let mut result = 0u32;
    let mut i = 1u32;
    
    while i <= n
        invariant 
            1 <= i <= n + 1,
            result == sum((i - 1) as nat),
            i <= u32::MAX,
            result <= u32::MAX - i,
        decreases n + 1 - i
    {
        result = result + i;
        i = i + 1;
    }
    
    proof {
        assert(i == n + 1);
        assert(result == sum(n as nat));
    }
    
    result
}
// </vc-code>

fn main() {}

}