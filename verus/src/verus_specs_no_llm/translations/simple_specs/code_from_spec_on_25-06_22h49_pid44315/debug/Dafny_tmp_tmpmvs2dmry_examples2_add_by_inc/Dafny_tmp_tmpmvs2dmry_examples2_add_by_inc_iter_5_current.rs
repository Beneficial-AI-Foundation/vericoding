use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn add_by_inc(x: nat, y: nat) -> (z: nat)
    ensures
        z == x + y
{
    let mut result: nat = x;
    let mut counter: nat = 0;
    
    while counter < y
        invariant
            result == x + counter,
            counter <= y,
    {
        result = result + 1;
        counter = counter + 1;
    }
    
    result
}

}