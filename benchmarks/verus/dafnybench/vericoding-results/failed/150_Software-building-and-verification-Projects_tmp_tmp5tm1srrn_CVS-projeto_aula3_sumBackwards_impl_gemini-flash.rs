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
proof fn lemma_sum_inductive(j: nat, total: nat)
    requires total == sum(j)
    ensures total + (j + 1) == sum( (j as int + 1) as nat)
{
    if j > 0 {
        assert(sum((j as int + 1) as nat) == (j as int + 1) + sum(j));
        // assert(total + (j + 1) == sum(j) + (j+1)); // This assertion is redundant given the above and the 'requires' clause.
    } else { // j == 0
        assert(sum((j as int + 1) as nat) == sum(1)); // sum(1) is 1.
        assert(total == sum(0)); // sum(0) is 0.
        // assert(total + (j+1) == 0 + 1); // This assertion is redundant given the above and the 'requires' clause.
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut j: u32 = 0;
    let mut total: u32 = 0;

    proof {
        assert(total as nat == sum(0));
    }

    while j <= n
        invariant
            j <= n + 1,
            total as nat == sum(j as nat),
            n >= 0, // Assuming n is non-negative since it's a u32 and used as nat.
        decreases (n as int + 1) - (j as int)
    {
        if j == n {
            break;
        }
        proof {
            lemma_sum_inductive(j as nat, total as nat);
        }
        total = total + (j + 1); 
        j = j + 1;
    }

    total
}
// </vc-code>

fn main() {}

}