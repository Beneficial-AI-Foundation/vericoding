use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn abs(x: int) -> (y: int)
    ensures y >= 0 && (x >= 0 ==> y == x) && (x < 0 ==> y == -x)
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

fn foo(x: int) -> (result: int)
    requires x >= 0
    ensures result >= 0
{
    let temp = abs(x);
    // Since x >= 0 (from precondition) and temp comes from abs(x),
    // we know from abs's postcondition that temp >= 0 and temp == x
    assert(temp >= 0); // From abs postcondition
    assert(temp == x) by {
        // From abs postcondition: (x >= 0 ==> temp == x)
        // We have x >= 0 from precondition
        // Therefore temp == x by modus ponens
        assert(x >= 0); // From precondition
    };
    temp
}

}