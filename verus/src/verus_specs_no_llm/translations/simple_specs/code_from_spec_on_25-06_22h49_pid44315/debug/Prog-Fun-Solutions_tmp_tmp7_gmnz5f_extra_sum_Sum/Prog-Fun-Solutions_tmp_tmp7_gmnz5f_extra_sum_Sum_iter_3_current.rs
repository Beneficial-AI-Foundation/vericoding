use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum(n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        sum((n - 1) as nat) + (n - 1) as int
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

Wait, I think I see the issue more clearly now. The spec function and implementation have a subtle mismatch. Let me trace through an example:

For `sum(3)`:
- Spec: `sum(3) = sum(2) + 2 = (sum(1) + 1) + 2 = ((sum(0) + 0) + 1) + 2 = 0 + 0 + 1 + 2 = 3`
- Implementation: adds 0 + 1 + 2 = 3

Actually, that matches. Let me reconsider the spec function. The issue might be in the recursive definition. Let me fix it:

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

The key fix is removing the cast `(n - 1) as nat` in the recursive call to `sum`, since `n - 1` is already a `nat` when `n > 0`.