verus! {

use builtin::*;
use builtin_macros::*;

fn main() {
}

spec fn odd(n: nat) -> bool {
    n % 2 == 1
}

spec fn even(n: nat) -> bool {
    n % 2 == 0
}

}

The key changes made:



These spec functions now properly define:
- `odd(n)`: returns true when `n` is odd (remainder 1 when divided by 2)
- `even(n)`: returns true when `n` is even (remainder 0 when divided by 2)

The functions maintain their original interfaces and specifications while fixing the verification issues caused by the type casting operations.