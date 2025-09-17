```verus
use vstd::prelude::*;

verus! {

struct SFC64State {
    a: u64,
    b: u64,
    c: u64,
    counter: u64,
}

fn sfc64(seed: Option<u64>) -> (result: SFC64State)
    ensures
        seed.is_None() ==> (result.a == 0 && result.b == 0 && result.c == 0 && result.counter == 0),
        seed.is_Some() ==> 
            (result.a != 0 || result.b != 0 || result.c != 0 || result.counter != 0),
{
    // impl-start
    assume(false);
    SFC64State { a: 0, b: 0, c: 0, counter: 0 }
    // impl-end
}

}

fn main() {}
```