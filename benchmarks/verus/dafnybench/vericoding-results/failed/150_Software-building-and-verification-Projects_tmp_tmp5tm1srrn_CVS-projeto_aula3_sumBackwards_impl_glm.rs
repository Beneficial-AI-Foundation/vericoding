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
proof fn sum_def(i: nat)
    requires i > 0
    ensures sum(i) == i + sum(i - 1)
{
    assert(sum(i) == i + sum(i - 1));
}
// </vc-helpers>

// <vc-spec>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut total: u32 = 0;
    let mut i: u32 = n;
    while i > 0 
        invariant 
            total as nat + sum(i as nat) == sum(n as nat),
            i <= n
        decreases i
    {
        proof {
            sum_def(i as nat);
        }
        total = total + i;
        i = i - 1;
    }
    total
}
// </vc-code>

fn main() {}

}