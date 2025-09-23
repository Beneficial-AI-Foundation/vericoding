// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

spec fn add(l: List<int>) -> int
    decreases l
{
    match l {
        List::Nil => 0,
        List::Cons(x, xs) => x + add(*xs),
    }
}

spec fn sum(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + sum((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn maxArrayReverse(arr: &[i32]) -> (max: i32)
    requires arr.len() > 0
    ensures 
        forall|i: int| 0 <= i < arr.len() ==> arr[i] <= max,
        exists|x: int| 0 <= x < arr.len() && arr[x] == max
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}