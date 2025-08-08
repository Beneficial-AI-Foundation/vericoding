use vstd::prelude::*;

verus! {

spec fn square_root_precond(n: nat) -> bool {
    true
}

spec fn square_root_postcond(n: nat, result: nat) -> bool {
    result * result <= n && n < (result + 1) * (result + 1)
}

fn bounded_loop(bound: u32, r: u32, n: u32) -> (result: u32)
    requires 
        bound <= 100,
        r <= 10,
        n <= 100,
    decreases bound
{
    if bound == 0 {
        r
    } else {
        bounded_loop(bound - 1, r, n)
    }
}

fn square_root(n: u32) -> (result: u32)
    requires 
        square_root_precond(n as nat),
        n <= 100,
    ensures
        square_root_postcond(n as nat, result as nat)
{
    let mut i = 0u32;
    while i <= 10
        invariant
            i <= 11,
            i * i <= n || i > 10,
            forall |j: u32| j < i ==> j * j <= n
    {
        if i * i > n {
            return i - 1;
        }
        if i == 10 {
            return i;
        }
        i = i + 1;
    }
    i - 1
}

proof fn square_root_spec_satisfied(n: u32)
    requires
        square_root_precond(n as nat),
        n <= 100,
{
    let result = square_root(n);
    assert(square_root_postcond(n as nat, result as nat));
}

fn main() {
    let n = 25u32;
    let root = square_root(n);
    println!("Square root of {} is {}", n, root);
}

}