Actually, the spec function looks correct. The issue might be in the loop invariant or the loop body. Let me fix this:

use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        sum(n - 1) + (n - 1) as int
    }
}

fn main() {
}

fn Sum(n: nat) -> (s: int)
    ensures
        s == sum(n)
{
    if n == 0 {
        return 0;
    }
    
    let mut total: int = 0;
    let mut i: nat = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            total == sum(i)
        decreases n - i
    {
        total = total + i as int;
        i = i + 1;
    }
    
    return total;
}

}

Wait, I think I see the issue. The loop is correct, but I need to make sure Verus can prove that the invariant is maintained. Let me add some proof hints and make sure the types are handled correctly:

use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        sum(n - 1) + (n - 1) as int
    }
}

fn main() {
}

fn Sum(n: nat) -> (s: int)
    ensures
        s == sum(n)
{
    if n == 0 {
        return 0;
    }
    
    let mut total: int = 0;
    let mut i: nat = 0;
    
    while i < n
        invariant
            i <= n,
            total == sum(i)
        decreases n - i
    {
        total = total + i as int;
        i = i + 1;
        
        // Proof hint: after incrementing i, we need total == sum(i)
        // We have: new_total = old_total + old_i
        //          new_i = old_i + 1
        // We need: new_total == sum(new_i)
        // That is: old_total + old_i == sum(old_i + 1)
        // By definition: sum(old_i + 1) = sum(old_i) + old_i
        // And we know: old_total == sum(old_i)
        // So: old_total + old_i == sum(old_i) + old_i == sum(old_i + 1) ✓
    }
    
    return total;
}

}