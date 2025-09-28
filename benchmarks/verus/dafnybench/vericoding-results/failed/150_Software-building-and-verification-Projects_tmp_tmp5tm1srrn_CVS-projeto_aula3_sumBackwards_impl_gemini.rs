// <vc-preamble>
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

spec fn sum(n: nat) -> nat 
    decreases n
{
    if n == 0 { 
        0 
    } else { 
        n + sum((n-1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added sum monotonicity lemma */
proof fn sum_plus_one(i: nat)
    ensures
        sum(i + 1) == sum(i) + i + 1,
{
}

proof fn sum_is_monotonic(a: nat, b: nat)
    requires
        a <= b,
    ensures
        sum(a) <= sum(b),
    decreases b - a
{
    if a < b {
        sum_is_monotonic(a, (b - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using u32 types and added proofs for loop invariants */
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    while i < n
        invariant
            i <= n,
            s as nat == sum(i as nat),
        decreases n - i
    {
        proof {
            sum_plus_one(i as nat);
            if i < n {
                sum_is_monotonic((i + 1) as nat, n as nat);
            }
        }

        i = i + 1;
        s = s + i;
    }
    s
}
// </vc-code>

}
fn main() {}