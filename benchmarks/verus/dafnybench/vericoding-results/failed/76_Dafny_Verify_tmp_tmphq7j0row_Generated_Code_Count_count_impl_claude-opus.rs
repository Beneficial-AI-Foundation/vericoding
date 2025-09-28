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
proof fn has_count_zero(v: int, a: Seq<int>)
    ensures has_count(v, a, 0) == 0
{
}

proof fn has_count_step(v: int, a: Seq<int>, n: nat)
    requires n > 0, n <= a.len()
    ensures has_count(v, a, n) == has_count(v, a, (n-1) as nat) + if a[(n-1) as int] == v { 1int } else { 0int }
{
}

proof fn map_values_index(a: Seq<i32>, i: int)
    requires 0 <= i < a.len()
    ensures a.map_values(|x: i32| x as int)[i] == a[i] as int
{
}

proof fn has_count_lemma(v: int, a: Seq<int>, i: nat)
    requires i < a.len()
    ensures has_count(v, a, (i + 1) as nat) == has_count(v, a, i as nat) + if a[i as int] == v { 1int } else { 0int }
{
    has_count_step(v, a, (i + 1) as nat);
}
// </vc-helpers>

// <vc-spec>
fn count(v: i32, a: &[i32], n: usize) -> (r: i32)
    requires n <= a.len()
    ensures n <= a.len() ==> has_count(v as int, a@.map_values(|x: i32| x as int), n as nat) == r as int
// </vc-spec>
// <vc-code>
{
    let mut count: i32 = 0;
    let mut i: usize = 0;
    
    while i < n
        invariant 
            i <= n,
            n <= a.len(),
            has_count(v as int, a@.map_values(|x: i32| x as int), i as nat) == count as int,
            count <= i32::MAX - 1,  // Prevent overflow
        decreases n - i
    {
        let old_i = i;
        let old_count = count;
        
        if a[i] == v {
            count = count + 1;
        }
        
        i = i + 1;
        
        // Prove the invariant is maintained
        proof {
            let mapped = a@.map_values(|x: i32| x as int);
            map_values_index(a@, old_i as int);
            assert(mapped[old_i as int] == a@[old_i as int] as int);
            
            has_count_lemma(v as int, mapped, old_i as nat);
            
            if a@[old_i as int] == v {
                assert(count == old_count + 1);
                assert(mapped[old_i as int] == v as int);
                assert(has_count(v as int, mapped, i as nat) == has_count(v as int, mapped, old_i as nat) + 1);
                assert(has_count(v as int, mapped, i as nat) == old_count as int + 1);
                assert(has_count(v as int, mapped, i as nat) == count as int);
            } else {
                assert(count == old_count);
                assert(mapped[old_i as int] != v as int);
                assert(has_count(v as int, mapped, i as nat) == has_count(v as int, mapped, old_i as nat));
                assert(has_count(v as int, mapped, i as nat) == old_count as int);
                assert(has_count(v as int, mapped, i as nat) == count as int);
            }
        }
    }
    
    count
}
// </vc-code>

fn main() {
}

}