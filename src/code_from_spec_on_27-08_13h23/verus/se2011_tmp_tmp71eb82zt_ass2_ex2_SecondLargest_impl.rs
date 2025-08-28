use vstd::prelude::*;

verus! {

// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// <vc-helpers>
fn find_max(a: &[i32]) -> (max_idx: usize)
    requires a.len() > 0
    ensures
        0 <= max_idx < a.len(),
        forall |i: usize| 0 <= i < a.len() ==> a@[i] <= a@[max_idx]
{
    let mut max_idx = 0;
    let mut i = 1;

    while i < a.len()
        invariant
            0 <= max_idx < a.len(),
            0 <= i <= a.len(),
            forall |k: usize| 0 <= k < i ==> a@[k] <= a@[max_idx]
    {
        if a@[i] > a@[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    max_idx
}

fn find_second_max(a: &[i32], max_idx: usize) -> (sec_idx: usize)
    requires
        a.len() > 1,
        0 <= max_idx < a.len()
    ensures
        0 <= sec_idx < a.len(),
        sec_idx != max_idx,
        forall |i: usize| 0 <= i < a.len() && i != max_idx ==> a@[i] <= a@[sec_idx]
{
    let mut sec_idx = if max_idx == 0 { 1 } else { 0 };
    let mut i = 0;

    while i < a.len()
        invariant
            0 <= sec_idx < a.len(),
            sec_idx != max_idx,
            0 <= i <= a.len(),
            forall |k: usize| 0 <= k < i && k != max_idx ==> a@[k] <= a@[sec_idx]
    {
        if i != max_idx && a@[i] > a@[sec_idx] {
            sec_idx = i;
        }
        i = i + 1;
    }
    sec_idx
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn second_largest(a: &[i32]) -> (seclar: i32)
    requires a.len() > 0
    //ensures exists i :: 0 <= i < a.len() && forall j :: (0 <= j < a.len() && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
// </vc-spec>
// </vc-spec>

// <vc-code>
fn second_largest(a: &[i32]) -> (seclar: i32)
    requires a.len() > 0
    ensures
        exists |i: usize| 0 <= i < a.len() && (
            forall |j: usize| 0 <= j < a.len() && j != i ==> a@[i] >= a@[j]
        ) && seclar <= a@[i] && (
            forall |j: usize| 0 <= j < a.len() && j != i ==> seclar >= a@[j] || a@[j] == a@[i]
        )
{
    if a.len() == 1 {
        return a@[0];
    }
    let max_idx = find_max(a);
    let sec_idx = find_second_max(a, max_idx);
    a@[sec_idx]
}
// </vc-code>

fn main() {
}

}