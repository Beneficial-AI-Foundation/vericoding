use vstd::prelude::*;

verus! {

// Precondition for isEven - trivially true
spec fn isEven_precond(n: int) -> bool {
    true
}

// Postcondition for isEven
spec fn isEven_postcond(n: int, result: bool) -> bool {
    (result ==> n % 2 == 0) && (!result ==> n % 2 != 0)
}

// The isEven function implementation
fn isEven(n: i64) -> (result: bool)
    requires isEven_precond(n as int)
    ensures isEven_postcond(n as int, result)
{
    n % 2 == 0
}

// The specification is automatically satisfied by the ensures clause
// This lemma just demonstrates that the postcondition holds
proof fn isEven_spec_satisfied(n: i64, result: bool)
    requires isEven_precond(n as int) && result == (n % 2 == 0)
    ensures isEven_postcond(n as int, result)
{
    // The proof is straightforward by case analysis
    if result {
        // If result is true, then n % 2 == 0 by the precondition
        // So result ==> n % 2 == 0 is trivially true
        // And !result is false, so !result ==> n % 2 != 0 is trivially true
    } else {
        // If result is false, then n % 2 != 0 by the precondition
        // So !result ==> n % 2 != 0 is trivially true
        // And result is false, so result ==> n % 2 == 0 is trivially true
    }
}

fn main() {
    /* code modified by LLM (iteration 1): removed println! statements as they are not supported in Verus */
    let x = isEven(4);
    let y = isEven(5);
}

} // verus!