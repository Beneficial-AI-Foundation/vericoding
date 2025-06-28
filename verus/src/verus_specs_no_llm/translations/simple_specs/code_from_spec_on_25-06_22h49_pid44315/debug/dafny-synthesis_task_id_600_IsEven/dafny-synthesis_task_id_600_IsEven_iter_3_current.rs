use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsEven(n: int) -> (result: bool)
    ensures
        result <==> n % 2 == 0
{
    // Use bit manipulation to check evenness
    // A number is even if its least significant bit is 0
    // We can check this by using the fact that n & 1 == 0 for even numbers
    // But since we're working with int, we use a different approach
    
    // Convert the mathematical property to executable code
    // We know that n % 2 == 0 iff n is even
    // We can use division and multiplication to check this
    let quotient = n / 2;
    let reconstructed = quotient * 2;
    reconstructed == n
}

}