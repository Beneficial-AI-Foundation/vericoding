use vstd::prelude::*;

verus! {

// Helper lemma for multiplication and division properties
proof fn mul_div_lemma(x: int)
    ensures 
        (x * 3) % 3 == 0,
        (x * 3) / 3 == x,
        ((x * 3) / 3) * 3 == x * 3
{
    // These are fundamental properties of integer arithmetic that Verus can prove automatically
    // No explicit proof steps needed as these follow from the definition of division and modulo
}

spec fn triple_precond(x: int) -> bool {
    true
}

spec fn triple_postcond(x: int, result: int) -> bool {
    result / 3 == x && (result / 3) * 3 == result
}

fn triple(x: i32) -> (result: i32)
    requires 
        triple_precond(x as int),
        -700000000 <= x <= 700000000
    ensures 
        triple_postcond(x as int, result as int)
{
    proof {
        mul_div_lemma(x as int);
    }
    x * 3
}

fn main() {
    let result = triple(42);
    println!("Triple of 42 is: {}", result);
}

} // verus!