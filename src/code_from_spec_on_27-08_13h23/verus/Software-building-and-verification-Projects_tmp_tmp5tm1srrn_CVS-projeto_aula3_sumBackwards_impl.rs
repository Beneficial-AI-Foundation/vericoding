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
proof fn sum_lemma(n: nat)
    decreases n
{
    if n > 0 {
        sum_lemma((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
{
    let mut sum: u32 = 0;
    let mut i: u32 = n;
    while i > 0
        invariant
            sum == sum((n - i) as nat),
            i <= n
        decreases i
    {
        sum = sum + i;
        i = i - 1;
    }
    proof {
        sum_lemma(n as nat);
    }
    sum
}
// </vc-code>

fn main() {}

}