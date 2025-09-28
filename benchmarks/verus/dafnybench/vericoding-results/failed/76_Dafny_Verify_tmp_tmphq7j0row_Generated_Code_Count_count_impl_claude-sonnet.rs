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
proof fn lemma_has_count_monotonic(v: int, a: Seq<int>, n: nat, m: nat)
    requires n <= m <= a.len()
    ensures has_count(v, a, n) <= has_count(v, a, m)
    decreases m - n
{
    if n < m {
        lemma_has_count_monotonic(v, a, n, (m-1) as nat);
    }
}

proof fn lemma_has_count_step(v: int, a: Seq<int>, n: nat)
    requires n < a.len()
    ensures has_count(v, a, (n+1) as nat) == has_count(v, a, n) + (if a[n as int] == v { 1int } else { 0int })
{
}

proof fn lemma_has_count_bound(v: int, a: Seq<int>, n: nat)
    requires n <= a.len()
    ensures has_count(v, a, n) <= n as int
    decreases n
{
    if n > 0 {
        lemma_has_count_bound(v, a, (n-1) as nat);
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
    let mut count = 0;
    let mut i = 0;
    
    proof {
        lemma_has_count_bound(v as int, a@.map_values(|x: i32| x as int), n as nat);
    }
    
    while i < n
        invariant 
            i <= n,
            n <= a.len(),
            count == has_count(v as int, a@.map_values(|x: i32| x as int), i as nat),
            count <= i as i32
        decreases n - i
    {
        assert(a@.map_values(|x: i32| x as int)[i as int] == a[i as int] as int);
        
        proof {
            lemma_has_count_step(v as int, a@.map_values(|x: i32| x as int), i as nat);
        }
        
        if a[i] == v {
            count = count + 1;
        }
        
        i = i + 1;
        
        assert(count == has_count(v as int, a@.map_values(|x: i32| x as int), i as nat));
    }
    
    count
}
// </vc-code>

fn main() {
}

}