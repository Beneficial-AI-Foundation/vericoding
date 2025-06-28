// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsArmstrong(n: int) -> (result: bool)
    requires
        100 <= n < 1000
    ensures
        result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
{
    let hundreds = n / 100;
    let tens = (n / 10) % 10;
    let units = n % 10;
    
    let sum_of_cubes = hundreds * hundreds * hundreds + tens * tens * tens + units * units * units;
    
    return n == sum_of_cubes;
}

}