use vstd::prelude::*;

verus! {

spec fn fib(n: nat) -> nat 
    decreases n
{
    if n == 0 { 
        1 
    } else if n == 1 { 
        1 
    } else { 
        fib((n-1) as nat) + fib((n-2) as nat)
    }
}


// 2.
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>)
}

spec fn add(l: List<int>) -> int 
    decreases l
{
    match l {
        List::Nil => 0,
        List::Cons(x, xs) => x + add(*xs)
    }
}


// 3.

// 5.

// 6
spec fn sum(n: nat) -> nat 
    decreases n
{
    if n == 0 { 
        0 
    } else { 
        n + sum((n-1) as nat)
    }
}

// <vc-helpers>
proof fn sum_unfold(n: nat)
    ensures n == 0 ==> sum(n) == 0,
            n > 0 ==> sum(n) == n + sum((n-1) as nat)
{
    // This follows directly from the definition of sum
}

proof fn sum_difference_lemma(n: nat, i: nat)
    requires i <= n,
             i > 0
    ensures sum(n) - sum(i) + i == sum(n) - sum((i - 1) as nat)
{
    assert(sum(i) == i + sum((i - 1) as nat)) by {
        sum_unfold(i);
    }
    assert(sum(n) - sum(i) + i == sum(n) - (i + sum((i - 1) as nat)) + i);
    assert(sum(n) - (i + sum((i - 1) as nat)) + i == sum(n) - sum((i - 1) as nat));
}
// </vc-helpers>

// <vc-spec>
fn sum_backwards(n: u32) -> (r: u32)
    ensures r == sum(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = n;
    let mut acc: u32 = 0;
    
    while i > 0
        invariant 
            i <= n,
            acc == sum(n as nat) - sum(i as nat),
            acc <= sum(n as nat),
            acc + i <= sum(n as nat),
        decreases i
    {
        let old_i = i;
        let old_acc = acc;
        
        acc = acc + i;
        i = i - 1;
        
        proof {
            assert(old_i > 0);
            assert(old_acc == sum(n as nat) - sum(old_i as nat));
            sum_difference_lemma(n as nat, old_i as nat);
            assert(acc == old_acc + old_i);
            assert(acc == sum(n as nat) - sum(old_i as nat) + old_i);
            assert(acc == sum(n as nat) - sum((old_i - 1) as nat));
            assert(i == old_i - 1);
            assert(acc == sum(n as nat) - sum(i as nat));
            
            // For overflow prevention
            if i as nat > 0 {
                assert(sum(i as nat) == i as nat + sum((i as nat - 1) as nat)) by {
                    sum_unfold(i as nat);
                }
                assert(acc == sum(n as nat) - sum(i as nat));
                assert(acc + i <= sum(n as nat));
            }
        }
    }
    
    assert(i == 0);
    assert(sum(0 as nat) == 0) by { sum_unfold(0 as nat); }
    assert(acc == sum(n as nat) - 0);
    
    acc
}
// </vc-code>

fn main() {}

}