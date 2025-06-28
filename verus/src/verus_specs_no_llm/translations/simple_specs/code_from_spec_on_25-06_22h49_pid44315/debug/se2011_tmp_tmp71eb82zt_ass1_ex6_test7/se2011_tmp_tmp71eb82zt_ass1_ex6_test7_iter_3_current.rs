use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Ceiling7(n: nat) -> (k: nat)
    requires n >= 0
    ensures k == n - (n % 7)
{
    proof {
        assert(n % 7 <= n) by {
            mod_range(n as int, 7);
        };
    }
    n - (n % 7)
}

fn test7(n: nat) -> (k: nat)
    requires n >= 0
    ensures k == n - (n % 7)
{
    proof {
        assert(n % 7 <= n) by {
            mod_range(n as int, 7);
        };
    }
    n - (n % 7)
}

}