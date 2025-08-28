use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}


// 2.
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


// 3.

// 5.

// 6
spec fn sum(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + sum((n - 1) as nat) }
}

// <vc-helpers>
spec fn max_in_range(arr: Seq<i32>, start: nat, end: nat) -> i32
    decreases end - start
{
    if start >= end {
        i32::MIN
    } else if start + 1 == end {
        arr[start]
    } else {
        let mid = (start + end) / 2;
        let left_max = max_in_range(arr, start, mid);
        let right_max = max_in_range(arr, mid, end);
        if left_max > right_max {
            left_max
        } else {
            right_max
        }
    }
}

proof fn prove_max_in_range(arr: Seq<i32>, start: nat, end: nat)
    requires start <= end, end <= arr.len()
    ensures
        forall|i: int| start <= i < end ==> arr[i] <= max_in_range(arr, start, end),
        exists|i: int| start <= i < end && arr[i] == max_in_range(arr, start, end)
    decreases end - start
{
    if start + 1 == end {
        assert(forall|i: int| start <= i < end ==> arr[i] <= max_in_range(arr, start, end));
        assert(arr[start] == max_in_range(arr, start, end));
    } else if start < end {
        let mid = (start + end) / 2;
        prove_max_in_range(arr, start, mid);
        prove_max_in_range(arr, mid, end);
        let left_max = max_in_range(arr, start, mid);
        let right_max = max_in_range(arr, mid, end);
        let overall_max = if left_max > right_max { left_max } else { right_max };
        assert(forall|i: int| start <= i < mid ==> arr[i] <= left_max);
        assert(forall|i: int| mid <= i < end ==> arr[i] <= right_max);
        assert(forall|i: int| start <= i < end ==> arr[i] <= overall_max);
        if left_max > right_max {
            assert(exists|i: int| start <= i < mid && arr[i] == left_max);
        } else {
            assert(exists|i: int| mid <= i < end && arr[i] == right_max);
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn maxArrayReverse(arr: &[i32]) -> (max: i32)
    requires arr.len() > 0
    ensures forall|i: int| 0 <= i < arr.len() ==> arr[i] <= max
    ensures exists|x: int| 0 <= x < arr.len() && arr[x] == max
// </vc-spec>
// </vc-spec>

// <vc-code>
fn maxArrayReverse(arr: &[i32]) -> (max: i32)
    requires arr.len() > 0
    ensures
        forall|i: int| 0 <= i < arr.len() ==> arr[i] <= max,
        exists|x: int| 0 <= x < arr.len() && arr[x] == max
{
    let mut max_val = arr[0];
    let mut i = arr.len() - 1;
    while i > 0
        invariant
            0 <= i < arr.len() || i == 0,
            forall|j: int| i < j < arr.len() ==> arr[j] <= max_val,
            exists|x: int| i < x < arr.len() && arr[x] == max_val
    {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        i = i - 1;
    }
    if arr[0] > max_val {
        max_val = arr[0];
    }
    proof {
        prove_max_in_range(arr@, 0, arr.len() as nat);
    }
    max_val
}
// </vc-code>

fn main() {
}

}