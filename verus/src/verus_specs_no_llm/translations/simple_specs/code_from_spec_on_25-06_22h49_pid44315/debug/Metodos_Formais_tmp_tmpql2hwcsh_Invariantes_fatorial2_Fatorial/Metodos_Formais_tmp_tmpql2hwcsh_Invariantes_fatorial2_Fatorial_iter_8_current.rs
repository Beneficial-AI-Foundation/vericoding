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
        let rec_result = Fatorial((n - 1) as nat);
        let result = n * rec_result;
        
        assert(result == Fat(n)) by {
            assert(Fat(n) == n * Fat((n - 1) as nat));
            assert(rec_result == Fat((n - 1) as nat));
        };
        
        result
    }
}

}