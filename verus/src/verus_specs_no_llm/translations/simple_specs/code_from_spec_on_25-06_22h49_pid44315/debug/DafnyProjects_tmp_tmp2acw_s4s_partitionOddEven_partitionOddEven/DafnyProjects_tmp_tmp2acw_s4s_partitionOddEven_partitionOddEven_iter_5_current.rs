verus! {

use builtin::*;
use builtin_macros::*;

fn main() {
}

spec fn odd(n: nat) -> bool {
    (n as int) % 2 == 1
}

spec fn even(n: nat) -> bool {
    (n as int) % 2 == 0
}

}