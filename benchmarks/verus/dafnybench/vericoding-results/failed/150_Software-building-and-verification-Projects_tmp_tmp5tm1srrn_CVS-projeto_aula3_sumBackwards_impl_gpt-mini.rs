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
// No helpers required for the iterative implementation.
// </vc-helpers>

// <vc-spec>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = n;
    let mut r: u32 = 0;

    while i != 0
        invariant (r as nat) + sum(i as nat) == sum(n as nat);
        invariant i <= n;
        decreases i;
    {
        let old_i = i;
        let old_r = r;
        // update
        r = old_r + old_i;
        i = old_i - 1;

        proof {
            // From the loop invariant before the update:
            assert(old_r as nat + sum(old_i as nat) == sum(n as nat));

            // old_i > 0 holds because we are in the loop body
            assert(old_i > 0);

            // By definition of spec fn sum for old_i > 0:
            assert(sum(old_i as nat) == old_i as nat + sum((old_i - 1) as nat));

            // Combine to get the new invariant:
            assert((old_r as nat + old_i as nat) + sum((old_i - 1) as nat) == sum(n as nat));
            assert(r as nat + sum(i as nat) == sum(n as nat));
        }
    }

    // After loop, i == 0, so invariant yields r as nat == sum(n as nat)
    assert(i == 0);
    assert((r as nat) + sum(0) == sum(n as nat));
    assert(r as nat == sum(n as nat));
    r
}
// </vc-code>

fn main() {}

}