use vstd::prelude::*;

verus! {

pub fn Search1000(a: &[i32], x: i32) -> (k: usize)
    requires 
        a.len() >= 1000,
        forall|p: usize, q: usize| 0 <= p < q < 1000 ==> a[p as int] <= a[q as int],
    ensures 
        0 <= k <= 1000,
        forall|r: usize| 0 <= r < k ==> a[r as int] < x,
        forall|r: usize| k <= r < 1000 ==> a[r as int] >= x,
{
}

pub open spec fn Is2Pow(n: int) -> bool
    decreases n
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n % 2 == 0 && Is2Pow(n / 2)
}

pub fn Search2PowLoop(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    requires 
        0 <= i <= i + n <= a.len(),
        forall|p: usize, q: usize| i <= p < q < i + n ==> a[p as int] <= a[q as int],
        Is2Pow((n + 1) as int),
    ensures 
        i <= k <= i + n,
        forall|r: usize| i <= r < k ==> a[r as int] < x,
        forall|r: usize| k <= r < i + n ==> a[r as int] >= x,
{
}

pub fn Search2PowRecursive(a: &[i32], i: usize, n: usize, x: i32) -> (k: usize)
    requires 
        0 <= i <= i + n <= a.len(),
        forall|p: usize, q: usize| i <= p < q < i + n ==> a[p as int] <= a[q as int],
        Is2Pow((n + 1) as int),
    ensures 
        i <= k <= i + n,
        forall|r: usize| i <= r < k ==> a[r as int] < x,
        forall|r: usize| k <= r < i + n ==> a[r as int] >= x,
{
}

}