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
proof fn lemma_sum_backwards_eq_fwd(n: nat)
    ensures
        sum(n) == n + if n > 0 { sum((n-1) as nat) } else { 0 },
    decreases n
{
    if n > 0 {
        lemma_sum_backwards_eq_fwd((n-1) as nat);
    }
}

proof fn lemma_sum_correct(i: nat, res: nat, n: nat)
    requires
        i <= n,
        res + sum(i) == sum(n),
    ensures
        (if i > 0 { res + i + sum((i-1) as nat) == sum(n) } else { true }),
    decreases i
{
    if i > 0 {
        lemma_sum_backwards_eq_fwd(i);
    }
}

proof fn lemma_sum_step(i: nat, res: nat, n: nat)
    requires
        i > 0,
        i <= n,
        res + i + sum((i-1) as nat) == sum(n),
    ensures
        (res + i) + sum((i-1) as nat) == sum(n),
    decreases i
{
}
// </vc-helpers>

// <vc-spec>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i = n;
    let mut res = 0u32;
    while i > 0
        invariant
            i <= n,
            res as nat + sum(i as nat) == sum(n as nat),
        decreases i
    {
        lemma_sum_correct(i as nat, res as nat, n as nat);
        res = (res + i);
        i = i - 1;
        lemma_sum_step((i + 1) as nat, (res - (i + 1)) as nat, n as nat);
    }
    res
}
// </vc-code>

fn main() {}

}