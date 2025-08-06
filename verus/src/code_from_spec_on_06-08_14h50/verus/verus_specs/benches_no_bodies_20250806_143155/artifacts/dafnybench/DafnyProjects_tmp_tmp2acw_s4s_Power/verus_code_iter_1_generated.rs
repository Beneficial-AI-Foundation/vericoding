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
            assert(power(x, 0) == 1);
            assert(power(x, a + b) == power(x, b));
        } else {
            // Inductive case: power(x, a) * power(x, b) == x * power(x, a-1) * power(x, b)
            // By induction hypothesis: power(x, a-1) * power(x, b) == power(x, (a-1) + b)
            // So: x * power(x, a-1) * power(x, b) == x * power(x, (a-1) + b) == power(x, a + b)
            product_of_powers(x, (a - 1) as nat, b);
            assert(power(x, (a - 1) as nat) * power(x, b) == power(x, ((a - 1) as nat) + b));
            assert(power(x, a) == x * power(x, (a - 1) as nat));
            assert(((a - 1) as nat) + b == a + b - 1);
            assert(power(x, a + b) == x * power(x, (a + b - 1) as nat));
        }
    }

    // A demonstration of the power function
    proof fn test_power_function() {
        assert(power(2, 0) == 1);
        assert(power(2, 1) == 2);
        assert(power(2, 2) == 4);
        assert(power(2, 3) == 8);
        assert(power(-2, 2) == 4);
        assert(power(-2, 3) == -8);
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
            // Base case
        } else if n == 1 {
            // Base case
        } else if n % 2 == 0 {
            // Even case: use the lemma
            product_of_powers(x, n / 2, n / 2);
            power_dc_correct(x, n / 2);
        } else {
            // Odd case: use the lemma
            product_of_powers(x, ((n - 1) / 2) as nat, ((n - 1) / 2) as nat);
            power_dc_correct(x, ((n - 1) / 2) as nat);
        }
    }

    // Test the specification
    proof fn test_power_dc_spec() {
        power_dc_correct(2, 5);
        assert(power_dc_spec(2, 5) == 32);
        power_dc_correct(-2, 2);
        assert(power_dc_spec(-2, 2) == 4);
        power_dc_correct(-2, 1);
        assert(power_dc_spec(-2, 1) == -2);
        power_dc_correct(-2, 0);
        assert(power_dc_spec(-2, 0) == 1);
        power_dc_correct(0, 0);
        assert(power_dc_spec(0, 0) == 1);
    }
}

fn main() {
}