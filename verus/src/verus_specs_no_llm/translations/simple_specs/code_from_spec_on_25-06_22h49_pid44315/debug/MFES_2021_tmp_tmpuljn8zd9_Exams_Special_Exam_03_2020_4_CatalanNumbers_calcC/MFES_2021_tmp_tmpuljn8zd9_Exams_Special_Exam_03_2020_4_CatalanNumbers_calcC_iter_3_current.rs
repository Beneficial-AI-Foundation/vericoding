use builtin::*;
use builtin_macros::*;

verus! {

spec fn C(n: nat) -> nat
    decreases n, 0nat
{
    if n == 0 {
        1
    } else {
        catalan_sum(n - 1, 0)
    }
}

spec fn catalan_sum(n: nat, i: nat) -> nat
    decreases n, 1nat, n - i
{
    if i > n {
        0
    } else {
        C(i) * C(n - i) + catalan_sum(n, i + 1)
    }
}

fn main() {
}

fn calcC(n: nat) -> (res: nat)
    ensures
        res == C(n)
    decreases n, 0nat
{
    if n == 0 {
        1
    } else {
        calcC_helper(n - 1, 0)
    }
}

fn calcC_helper(n: nat, i: nat) -> (res: nat)
    ensures
        res == catalan_sum(n, i)
    decreases n, 1nat, n - i
{
    if i > n {
        0
    } else {
        let left = calcC(i);
        let right = calcC(n - i);
        let rest = calcC_helper(n, i + 1);
        left * right + rest
    }
}

}