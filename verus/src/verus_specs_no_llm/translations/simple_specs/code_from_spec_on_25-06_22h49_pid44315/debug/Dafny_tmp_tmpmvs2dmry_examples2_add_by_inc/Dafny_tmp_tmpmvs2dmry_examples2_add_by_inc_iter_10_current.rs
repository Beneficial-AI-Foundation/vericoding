use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn add_by_inc(x: u32, y: u32) -> (z: u32)
    requires
        x + y <= 0xFFFFFFFF,  // Ensure no overflow
    ensures
        z == x + y
{
    let mut result: u32 = x;
    let mut counter: u32 = 0;
    
    while counter < y
        invariant
            result == x + counter,
            counter <= y,
            x + counter <= 0xFFFFFFFF,
            result <= 0xFFFFFFFF,
        decreases y - counter
    {
        assert(counter < y);
        assert(x + counter < x + y);
        assert(x + y <= 0xFFFFFFFF);
        assert(x + counter < 0xFFFFFFFF);
        assert(result == x + counter);
        assert(result < 0xFFFFFFFF);
        
        result = result + 1;
        counter = counter + 1;
        
        assert(result == x + counter);
    }
    
    result
}

}