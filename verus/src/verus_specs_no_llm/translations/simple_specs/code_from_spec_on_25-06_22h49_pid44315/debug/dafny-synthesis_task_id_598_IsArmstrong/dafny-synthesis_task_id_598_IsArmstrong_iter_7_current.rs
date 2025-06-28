use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

exec fn IsArmstrong(n: int) -> (result: bool)
    requires
        100 <= n < 1000
    ensures
        result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
{
    let hundreds = n / 100;
    let tens = (n / 10) % 10;
    let units = n % 10;
    
    let sum_of_cubes = hundreds * hundreds * hundreds + tens * tens * tens + units * units * units;
    
    // Prove that our computation matches the specification
    assert(hundreds == n / 100) by {
        // This is true by definition
    };
    
    assert(tens == (n / 10) % 10) by {
        // This is true by definition
    };
    
    assert(units == n % 10) by {
        // This is true by definition
    };
    
    assert(sum_of_cubes == hundreds * hundreds * hundreds + tens * tens * tens + units * units * units) by {
        // This is true by definition of sum_of_cubes
    };
    
    // The key insight: prove that our local variables match the specification expression
    assert(sum_of_cubes == (n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)) by {
        assert(hundreds * hundreds * hundreds == (n / 100) * (n / 100) * (n / 100));
        assert(tens * tens * tens == ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10));
        assert(units * units * units == (n % 10) * (n % 10) * (n % 10));
    };
    
    let result = n == sum_of_cubes;
    
    // Final assertion to help Verus connect our result to the postcondition
    assert(result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))) by {
        assert(result == (n == sum_of_cubes));
        assert(sum_of_cubes == (n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10));
    };
    
    result
}

}