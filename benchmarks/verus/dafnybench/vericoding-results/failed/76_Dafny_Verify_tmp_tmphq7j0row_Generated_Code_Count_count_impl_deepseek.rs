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
spec fn has_count_rec_lemma(v: int, a: Seq<int>, n: nat, k: nat) -> bool
    decreases n - k
{
    if k < n {
        has_count_rec_lemma(v, a, (n - 1) as nat, k)
    } else {
        true
    }
}

proof fn has_count_empty(v: int, a: Seq<int>, n: nat)
    ensures has_count(v, a, 0) == 0
{
}

proof fn has_count_zero(v: int, a: Seq<int>)
    ensures has_count(v, a, 0) == 0
{
}

proof fn has_count_cons(v: int, a: Seq<int>, n: nat)
    requires n > 0
    ensures has_count(v, a, n) == if a[n-1] == v { has_count(v, a, (n-1) as nat) + 1 } else { has_count(v, a, (n-1) as nat) }
{
}

proof fn has_count_subrange_base(v: int, a: Seq<int>)
    ensures has_count(v, a.subrange(0, 0), 0) == 0
{
}

proof fn has_count_subrange_lemma(v: int, a: Seq<int>, start: int, end: int, n: nat)
    requires 
        0 <= start <= end <= a.len(),
        n <= (end - start) as nat
    ensures has_count(v, a.subrange(start, end), n) == has_count(v, a, n)
    decreases n
{
    if n == 0 {
    } else {
        has_count_subrange_lemma(v, a, start, end, (n-1) as nat);
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
    let mut r: i32 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            r as int == has_count(v as int, a@.map_values(|x: i32| x as int), i as nat),
        decreases n - i
    {
        let idx = i;
        if a[idx] == v {
            r = r + 1;
        }
        i = i + 1;
        proof {
            has_count_cons(v as int, a@.map_values(|x: i32| x as int), i as nat);
        }
    }
    r
}
// </vc-code>

fn main() {
}

}