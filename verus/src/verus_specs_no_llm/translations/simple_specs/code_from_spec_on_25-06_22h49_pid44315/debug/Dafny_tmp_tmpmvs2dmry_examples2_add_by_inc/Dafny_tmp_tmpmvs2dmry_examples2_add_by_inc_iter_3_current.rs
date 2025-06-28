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
    
    // The loop condition is false, so counter >= y
    // Combined with the invariant counter <= y, we get counter == y
    assert(counter >= y); // Loop condition is false
    assert(counter <= y); // From invariant
    assert(counter == y); // Therefore counter == y
    assert(result == x + counter); // From invariant
    assert(result == x + y); // Substituting counter == y
    
    result
}

}