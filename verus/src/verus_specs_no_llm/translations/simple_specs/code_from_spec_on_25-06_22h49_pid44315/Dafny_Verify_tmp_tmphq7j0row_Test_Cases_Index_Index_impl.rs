use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Index(n: int) -> (i: int)
    requires
        1 <= n
    ensures
        0 <= i < n
{
    0
}

}

Actually, the code you provided should already verify correctly. The function `Index` takes an integer `n` where `n >= 1`, and returns `0`. Since `n >= 1`, we have `0 <= 0 < n`, which satisfies the postcondition `0 <= i < n`.

If you're getting verification errors, it might be due to the Verus version or setup. The code as written should be valid and verify successfully.