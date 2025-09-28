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
proof fn sum_unfold_strict(n: nat)
    requires n > 0
    ensures sum(n) == n + sum((n - 1) as nat)
{
    assert(n != 0);
    assert(sum(n) == if n == 0 { 0 } else { n + sum((n - 1) as nat) });
    assert(sum(n) == n + sum((n - 1) as nat));
}
// </vc-helpers>

// <vc-spec>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = n;
    let mut acc: u32 = 0;

    while i > 0
        invariant i <= n
        invariant (acc as nat) + sum(i as nat) == sum(n as nat)
        decreases i
    {
        proof {
            assert((i as nat) > 0);
            sum_unfold_strict(i as nat);
            assert(sum(i as nat) == (i as nat) + sum((i - 1) as nat));
        }
        acc = acc + i;
        i = i - 1;
    }

    assert(i == 0);
    assert(sum(0 as nat) == 0);
    assert((acc as nat) == sum(n as nat));
    acc
}
// </vc-code>

fn main() {}

}