use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

exec fn IsArmstrong(n: i32) -> (result: bool)
    requires
        100 <= n < 1000
    ensures
        result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
{
    let hundreds = n / 100;
    let tens = (n / 10) % 10;
    let units = n % 10;
    
    let sum_of_cubes = hundreds * hundreds * hundreds + tens * tens * tens + units * units * units;
    
    // The result is whether n equals the sum of cubes of its digits
    let result = n == sum_of_cubes;
    
    // Proof that our computation matches the specification
    assert(sum_of_cubes == (n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)) by {
        // Expand the definition of sum_of_cubes
        assert(sum_of_cubes == hundreds * hundreds * hundreds + tens * tens * tens + units * units * units);
        // Show that our local variables equal the specification expressions
        assert(hundreds == n / 100);
        assert(tens == (n / 10) % 10);
        assert(units == n % 10);
        // Therefore the sum_of_cubes equals the specification expression
    };
    
    // Establish the postcondition
    assert(result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10))));
    
    result
}

}