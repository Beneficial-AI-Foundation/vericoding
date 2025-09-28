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
spec fn sum_backwards_decreases(n: u32) -> nat {
    n as nat
}

spec fn ghost_sum_backwards(n: u32) -> u32
    decreases n
    ensures ghost_sum_backwards(n) == sum(n as nat)
{
    if n == 0 {
        0
    } else {
        n + ghost_sum_backwards(n - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
// </vc-spec>
// <vc-code>
{
    decreases n;
    if n == 0 {
        0
    } else {
        n + sum_backwards(n - 1)
    }
}
// </vc-code>

fn main() {}

}