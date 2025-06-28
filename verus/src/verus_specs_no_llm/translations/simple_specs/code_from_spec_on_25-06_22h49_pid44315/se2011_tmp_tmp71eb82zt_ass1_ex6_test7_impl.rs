use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Ceiling7(n: nat) -> (k: nat)
    ensures k == n + (7 - n % 7) % 7
{
    proof {
        if n % 7 == 0 {
            assert((7 - n % 7) % 7 == 0);
        } else {
            assert(n % 7 > 0);
            assert(n % 7 < 7);
            assert(7 - n % 7 > 0);
            assert(7 - n % 7 <= 7);
            assert((7 - n % 7) % 7 == 7 - n % 7);
        }
    }
    n + (7 - n % 7) % 7
}

fn test7(n: nat) -> (k: nat)
    ensures k == n + (7 - n % 7) % 7
{
    proof {
        if n % 7 == 0 {
            assert((7 - n % 7) % 7 == 0);
        } else {
            assert(n % 7 > 0);
            assert(n % 7 < 7);
            assert(7 - n % 7 > 0);
            assert(7 - n % 7 <= 7);
            assert((7 - n % 7) % 7 == 7 - n % 7);
        }
    }
    n + (7 - n % 7) % 7
}

}