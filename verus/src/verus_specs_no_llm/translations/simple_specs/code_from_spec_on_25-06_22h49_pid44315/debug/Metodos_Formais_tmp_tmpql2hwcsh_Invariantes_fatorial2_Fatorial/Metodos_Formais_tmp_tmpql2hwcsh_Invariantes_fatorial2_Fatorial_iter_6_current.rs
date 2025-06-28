use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Fat(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        n * Fat((n - 1) as nat)
    }
}

fn Fatorial(n: nat) -> (f: nat)
    ensures
        f == Fat(n)
    decreases n
{
    if n == 0 {
        1
    } else {
        assert(n >= 1);
        let rec_result = Fatorial((n - 1) as nat);
        assert(rec_result == Fat((n - 1) as nat)) by {
            // This follows from the postcondition of the recursive call
        };
        let result = n * rec_result;
        assert(result == n * Fat((n - 1) as nat)) by {
            // This follows from the previous assertion
        };
        assert(result == Fat(n)) by {
            // This follows from the definition of Fat when n > 0
            assert(Fat(n) == n * Fat((n - 1) as nat));
        };
        result
    }
}

}