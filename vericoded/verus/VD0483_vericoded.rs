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
/* code modified by LLM (iteration 3): fixed spec indexing to use `arr@[k]` instead of `arr[k as usize]`. */
{
    let mut max = arr[0];
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            1 <= i,
            i <= arr.len(),
            exists|k: int| 0 <= k < i as int && arr@[k] == max,
            forall|k: int| 0 <= k < i as int ==> arr@[k] <= max,
        decreases arr.len() - i
    {
        if arr[i] > max {
            max = arr[i];
        }
        i = i + 1;
    }
    max
}
// </vc-code>

}
fn main() {}