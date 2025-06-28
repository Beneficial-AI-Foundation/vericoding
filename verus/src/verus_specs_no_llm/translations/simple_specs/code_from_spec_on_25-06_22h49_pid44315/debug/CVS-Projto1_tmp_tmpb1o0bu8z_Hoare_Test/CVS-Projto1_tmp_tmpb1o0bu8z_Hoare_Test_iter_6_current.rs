use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Max(x: nat, y: nat) -> (r: nat)
    ensures r >= x && r >= y
    ensures r == x || r == y
{
    if x >= y {
        x
    } else {
        y
    }
}

// Test method that demonstrates Max works correctly
fn Test() -> (r: nat)
    ensures r >= 5 && r >= 3
    ensures r == 5 || r == 3
{
    let result = Max(5nat, 3nat);
    result
}

}