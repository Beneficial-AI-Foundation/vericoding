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
    //IMPL product_of_powers
    /* code modified by LLM (iteration 3): fixed multiplication associativity and strengthened proof steps */
    proof fn product_of_powers(x: int, a: nat, b: nat)
        ensures power(x, a) * power(x, b) == power(x, a + b)
        decreases a
    {
        if a == 0 {
            // Base case: power(x, 0) * power(x, b) == 1 * power(x, b) == power(x, b) == power(x, 0 + b)
            assert(power(x, 0) == 1);
            assert(power(x, 0 + b) == power(x, b));
            assert(power(x, 0) * power(x, b) == 1 * power(x, b));
            assert(1 * power(x, b) == power(x, b));
        } else {
            // Inductive step
            product_of_powers(x, (a - 1) as nat, b);
            assert(power(x, (a - 1) as nat) * power(x, b) == power(x, (a - 1) as nat + b));
            assert(power(x, a) == x * power(x, (a - 1) as nat));
            assert(power(x, a) * power(x, b) == x * power(x, (a - 1) as nat) * power(x, b));
            /* code modified by LLM (iteration 3): explicit associativity step to connect the multiplication */
            assert(x * power(x, (a - 1) as nat) * power(x, b) == x * (power(x, (a - 1) as nat) * power(x, b)));
            assert(x * (power(x, (a - 1) as nat) * power(x, b)) == x * power(x, (a - 1) as nat + b));
            assert((a - 1) as nat + b == (a + b - 1) as nat);
            assert(x * power(x, (a + b - 1) as nat) == power(x, a + b));
            /* code modified by LLM (iteration 3): final connection to complete the proof */
            assert(power(x, a) * power(x, b) == power(x, a + b));
        }
    }

    // A demonstration of the power function
    proof fn test_power_function() {
        assert(power(2, 0) == 1);
        assert(power(2, 1) == 2);
        assert(power(2, 2) == 4);
        assert(power(2, 3) == 8);
        /* code modified by LLM (iteration 1): added explicit computation steps for negative base */
        assert(power(-2, 2) == (-2) * power(-2, 1));
        assert(power(-2, 1) == (-2) * power(-2, 0));
        assert(power(-2, 0) == 1);
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

    /* code modified by LLM (iteration 2): added helper lemma to establish power(x, 1) == x */
    proof fn power_one_lemma(x: int)
        ensures power(x, 1) == x
    {
        assert(power(x, 1) == x * power(x, 0));
        assert(power(x, 0) == 1);
        assert(x * 1 == x);
    }

    // Proof that our divide-and-conquer algorithm equals the recursive definition
    /* code modified by LLM (iteration 2): use helper lemma and simplify assertions */
    proof fn power_dc_correct(x: int, n: nat)
        ensures power_dc_spec(x, n) == power(x, n)
        decreases n
    {
        if n == 0 {
            // Base case: both equal 1
            assert(power_dc_spec(x, 0) == 1);
            assert(power(x, 0) == 1);
        } else if n == 1 {
            // Base case: both equal x
            assert(power_dc_spec(x, 1) == x);
            power_one_lemma(x);
        } else if n % 2 == 0 {
            // Even case: n = 2k for some k = n/2
            let k = n / 2;
            power_dc_correct(x, k);
            assert(power_dc_spec(x, k) == power(x, k));
            assert(power_dc_spec(x, n) == power_dc_spec(x, k) * power_dc_spec(x, k));
            assert(power_dc_spec(x, k) * power_dc_spec(x, k) == power(x, k) * power(x, k));
            product_of_powers(x, k, k);
            assert(power(x, k) * power(x, k) == power(x, k + k));
            assert(k + k == n);
            assert(power(x, k + k) == power(x, n));
        } else {
            // Odd case: n = 2k + 1 for some k = (n-1)/2
            let k = ((n - 1) / 2) as nat;
            power_dc_correct(x, k);
            assert(power_dc_spec(x, k) == power(x, k));
            assert(power_dc_spec(x, n) == power_dc_spec(x, k) * power_dc_spec(x, k) * x);
            assert(power_dc_spec(x, k) * power_dc_spec(x, k) * x == power(x, k) * power(x, k) * x);
            product_of_powers(x, k, k);
            assert(power(x, k) * power(x, k) == power(x, k + k));
            assert(power(x, k) * power(x, k) * x == power(x, k + k) * x);
            power_one_lemma(x);
            product_of_powers(x, k + k, 1);
            assert(power(x, k + k) * power(x, 1) == power(x, k + k + 1));
            assert(k + k + 1 == 2 * k + 1);
            assert(2 * k + 1 == n);
            assert(power(x, k + k + 1) == power(x, n));
        }
    }

    // Test the specification
    /* code modified by LLM (iteration 2): use helper lemma and strengthen proof steps */
    proof fn test_power_dc_spec() {
        // Test power(2, 5) == 32
        power_one_lemma(2);
        assert(power(2, 1) == 2);
        assert(power(2, 2) == 2 * power(2, 1));
        assert(power(2, 2) == 4);
        assert(power(2, 3) == 2 * power(2, 2));
        assert(power(2, 3) == 8);
        assert(power(2, 4) == 2 * power(2, 3));
        assert(power(2, 4) == 16);
        assert(power(2, 5) == 2 * power(2, 4));
        assert(power(2, 5) == 32);
        
        power_dc_correct(2, 5);
        assert(power_dc_spec(2, 5) == power(2, 5));
        assert(power_dc_spec(2, 5) == 32);
        
        // Test power(-2, 2) == 4
        power_one_lemma(-2);
        assert(power(-2, 1) == -2);
        assert(power(-2, 2) == (-2) * power(-2, 1));
        assert(power(-2, 2) == (-2) * (-2));
        assert(power(-2, 2) == 4);
        
        power_dc_correct(-2, 2);
        assert(power_dc_spec(-2, 2) == power(-2, 2));
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
    println!("Power function verification complete!");
    println!("All proofs and tests have been verified.");
}