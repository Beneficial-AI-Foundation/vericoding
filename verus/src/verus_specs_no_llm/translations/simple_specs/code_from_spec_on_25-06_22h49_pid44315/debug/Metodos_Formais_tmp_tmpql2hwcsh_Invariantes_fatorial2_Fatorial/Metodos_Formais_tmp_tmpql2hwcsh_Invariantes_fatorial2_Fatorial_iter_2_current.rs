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
        n * Fat(n - 1)
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
        let rec_result = Fatorial(n - 1);
        assert(rec_result == Fat(n - 1));
        let result = n * rec_result;
        assert(result == n * Fat(n - 1));
        assert(result == Fat(n));
        result
    }
}

}