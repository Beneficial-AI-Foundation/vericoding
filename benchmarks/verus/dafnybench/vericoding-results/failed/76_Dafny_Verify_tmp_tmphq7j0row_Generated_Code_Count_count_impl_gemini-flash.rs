use vstd::prelude::*;

verus! {

spec fn has_count(v: int, a: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        if a[n-1] == v {
            has_count(v, a, (n-1) as nat) + 1
        } else {
            has_count(v, a, (n-1) as nat)
        }
    }
}

// <vc-helpers>
fn count_rec(v: i32, a: &[i32], n: usize, i: usize) -> (r: i32)
    requires i <= n
    requires n <= a.len()
    ensures has_count(v as int, a@.map_values(|x: i32| x as int), i as nat) == r as int
{
    if i == 0 {
        0
    } else {
        let prev_count = count_rec(v, a, n, i - 1);
        if a[i - 1] == v {
            prev_count + 1
        } else {
            prev_count
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn count(v: i32, a: &[i32], n: usize) -> (r: i32)
    requires n <= a.len()
    ensures n <= a.len() ==> has_count(v as int, a@.map_values(|x: i32| x as int), n as nat) == r as int
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        0
    } else {
        let mut count: i32 = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                i <= n,
                count == count_rec(v, a, n, i)
            decreases n - i
        {
            if a[i] == v {
                count = count + 1;
            }
            i = i + 1;
        }

        count
    }
}
// </vc-code>

fn main() {
}

}