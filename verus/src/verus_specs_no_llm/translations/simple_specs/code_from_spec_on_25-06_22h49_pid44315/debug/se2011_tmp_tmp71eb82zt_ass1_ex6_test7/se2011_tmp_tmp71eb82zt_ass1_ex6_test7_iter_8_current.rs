use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Ceiling7(n: nat) -> (k: nat)
    ensures k == n - (n % 7)
{
    // The modulo operation in Verus for nat types automatically ensures n % 7 <= n
    // So we can directly compute n - (n % 7)
    n - (n % 7)
}

fn test7(n: nat) -> (k: nat)
    ensures k == n - (n % 7)
{
    // Same implementation as Ceiling7
    n - (n % 7)
}

}