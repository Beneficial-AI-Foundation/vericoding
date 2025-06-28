use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn add_by_inc(x: nat, y: nat) -> (z: nat)
    ensures
        z == x + y
{
    let mut result = x;
    let mut counter = 0nat;
    
    while counter < y
        invariant
            result == x + counter,
            counter <= y,
    {
        result = result + 1;
        counter = counter + 1;
    }
    
    // At this point: result == x + counter and counter == y
    // Therefore: result == x + y
    assert(counter == y);
    assert(result == x + counter);
    assert(result == x + y);
    
    result
}

}