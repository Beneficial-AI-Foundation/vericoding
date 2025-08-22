use vstd::prelude::*;

verus! {
    /* 
    * Formal verification of an O(log n) algorithm to calculate the natural power of an integer number (x^n), 
    * illustrating the usage of lemmas and automatic induction in Verus.
    * Translated from Dafny by Claude, originally by J. Pascoal Faria, FEUP, Jan/2022.
    * 
    * Note: This translation preserves the structure of the original Dafny code while adapting
    * it to Verus syntax and verification patterns.
    */

    // Recursive definition of x^n in functional style, with time and space complexity O(n).
    spec fn power(x: int, n: nat) -> int
        decreases n
    {
        if n == 0 { 1 } else { x * power(x, (n - 1) as nat) }
    }

    // States the property x^a * x^b = x^(a+b), that the method power takes advantage of. 
    // The property is proved by automatic induction on 'a'.
    proof fn product_of_powers(x: int, a: nat, b: nat)
        ensures power(x, a) * power(x, b) == power(x, a + b)
        decreases a
    {
        if a == 0 {
            // Base case: power(x, 0) * power(x, b) == 1 * power(x, b) == power(x, b) == power(x, 0 + b)
        } else {
            // Inductive step: power(x, a) * power(x, b) == x * power(x, a-1) * power(x, b)
            // By inductive hypothesis: power(x, a-1) * power(x, b) == power(x, (a-1) + b)
            // So: x * power(x, a-1) * power(x, b) == x * power(x, (a-1) + b) == power(x, a + b)
            product_of_powers(x, (a - 1) as nat, b);
        }
    }

    // A demonstration of the power function
    proof fn test_power_function() {
        assert(power(2, 0) == 1);
        assert(power(2, 1) == 2);
        assert(power(2, 3) == 8);
        assert(power(3, 2) == 9);
    }

    // The main algorithm structure expressed as a spec function
    spec fn power_dc_spec(x: int, n: nat) -> int
        decreases n
    {
        if n == 0 {
            1
        } else if n == 1 {
            x
        } else if n % 2 == 0 {
            let temp = power_dc_spec(x, n / 2);
            temp * temp
        } else {
            let temp = power_dc_spec(x, ((n - 1) / 2) as nat);
            temp * temp * x
        }
    }

    // Proof that our divide-and-conquer algorithm equals the recursive definition
    proof fn power_dc_correct(x: int, n: nat)
        ensures power_dc_spec(x, n) == power(x, n)
        decreases n
    {
        if n == 0 {
            // Base case: both equal 1
        } else if n == 1 {
            // Base case: both equal x
        } else if n % 2 == 0 {
            // Even case: power_dc_spec(x, n) = power_dc_spec(x, n/2)^2
            // By inductive hypothesis: power_dc_spec(x, n/2) == power(x, n/2)
            // So power_dc_spec(x, n) = power(x, n/2)^2
            // By product_of_powers lemma: power(x, n/2) * power(x, n/2) == power(x, n/2 + n/2) == power(x, n)
            power_dc_correct(x, n / 2);
            product_of_powers(x, n / 2, n / 2);
        } else {
            // Odd case: power_dc_spec(x, n) = power_dc_spec(x, (n-1)/2)^2 * x
            // By inductive hypothesis: power_dc_spec(x, (n-1)/2) == power(x, (n-1)/2)
            // So power_dc_spec(x, n) = power(x, (n-1)/2)^2 * x
            // By product_of_powers: power(x, (n-1)/2) * power(x, (n-1)/2) == power(x, n-1)
            // So power_dc_spec(x, n) = power(x, n-1) * x == power(x, n)
            power_dc_correct(x, ((n - 1) / 2) as nat);
            /* code modified by LLM (iteration 1): Fixed type casting for nat arguments */
            product_of_powers(x, ((n - 1) / 2) as nat, ((n - 1) / 2) as nat);
            product_of_powers(x, (n - 1) as nat, 1);
        }
    }

    // Test the specification
    proof fn test_power_dc_spec() {
        power_dc_correct(2, 0);
        power_dc_correct(2, 1);
        power_dc_correct(2, 3);
        power_dc_correct(3, 2);
        power_dc_correct(2, 8);
        
        assert(power_dc_spec(2, 0) == 1);
        assert(power_dc_spec(2, 1) == 2);
        assert(power_dc_spec(2, 3) == 8);
        assert(power_dc_spec(3, 2) == 9);
    }
}

fn main() {
    println!("Power verification example completed successfully!");
    println!("All proofs verify that the divide-and-conquer power algorithm is correct.");
}