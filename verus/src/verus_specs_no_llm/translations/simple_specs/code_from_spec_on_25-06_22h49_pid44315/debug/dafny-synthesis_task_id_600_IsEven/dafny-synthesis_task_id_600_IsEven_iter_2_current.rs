use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsEven(n: int) -> (result: bool)
    ensures
        result <==> n % 2 == 0
{
    // For executable code with int, we need to handle the modulo operation carefully
    // We can use the fact that a number is even if its absolute value modulo 2 equals 0
    if n >= 0 {
        (n % 2) == 0
    } else {
        ((-n) % 2) == 0
    }
}

}