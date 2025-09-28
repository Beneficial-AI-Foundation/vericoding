use vstd::prelude::*;

verus! {

//Problem01

/*
3 Verification conditions

1. VC1: Precondiotion implies the loop variant
n ∈ ℕ => sqn = 0*0 ∧ i = 0 ∧ x=? ∧ i≤n 
n >= 0 => 0 = 0*0 ∧ i = 0 ∧ i≤n 
n >= 0 => 0 = 0*0 ∧ 0 ≤ n 
2. VC2: Loop invariant and loop guard preserve the loop invariant.
VC2: i < n ∧ i+1 ≤ n ∧ sqn = i * i ⇒ sqn = sqn + x ∧ i = i + 1 ∧ x = 2 * i + 1
3.VC3: Loop terminates, and the loop invariant implies the postcondition.
VC3: ¬(i < n) ∧ i ≤ n ∧ sqn = i * i ⇒ sqn = n * n

Simplified VC for square0
1. true, since 0 = 0 and n >= 0 => 0 ≤ n
2. true, i < n => i + 1 <= n
3. true, ¬(i < n) ∧ i ≤ n ∧ sqn = i * i ⇒ sqn = n * n since ¬(i < n) ∧ i ≤ n imply i = n

*/


//Problem02
//As you can see below, Verus claims that after executing the following function
//strange() we will have that 1=2;

/*(a). Do you have an explanation for this behaviour?
    Answer: 
    the function strange() doesn't have any input or output. This function initializes
    variable x with value 4. Then it calculates variable c as a result of calling
    function 'q' with x as first var and 2*x as second var.the strange function does not 
    specify any postcondition. Therefore, we cannot make any assumptions about the 
    behavior or the value of c after calling q.
    We can change ensures in strange() to false and it's still verified
*/

/*(b)
{
  assume{:axiom} false;
}var x:nat := 4; var c := q(x,2*x); {1 = 2 }
    precond in strange(): difference between 'y' and 'x' muss be greater than 2,
    square from 'z' will be a value  between 'x' and 'y'

    apply the Hoare rules step by step:
    1. {true} as a precondition
    2. we assign 4 to 'x' and having {4=4}
    3. assign value q(x, 2 * x) to c, substitute the postcondition of 'q' in place of 'c'
        post cond of q will be x < z*z < 2*x. Replacing c we having {x < z * z < 2 * x}
    4. we having the statement {x < z*z < 2*x} => {1 = 2} as postcondtion

    as we know the statment {1 = 2} is always false. true => false is always false     



*/

//Problem 3
//Use what you know about the weakest preconditions/strongest postconditions to ex-
//plain why the following code verifies:

/*
WP: is a condition that, if satisfied before the execution of a program, guarantees the 
satisfaction of a specified postcondition
SP: is a condition that must hold after the execution of a program, assuming a specified 
precondition

The strongest postcondition for assert is x<=9
Analyze the code: 
The strongest postcondition for the assert statement assert x <= 9; is x <= 9. This 
postcondition asserts that the value of x should be less than or equal to 9 after the 
execution of the program. To ensure this postcondition, we need to find a weakest precondition 
(WP) that guarantees x <= 9 after executing the code.

The "assume" statement introduces a precondition.
It assumes that the square of x is less than 100. In other words, it assumes that x is 
within the range (0, 10) since the largest possible square less than 100 is 9 * 9 = 81.


*/

// <vc-helpers>
fn no_square_between_4_8(z: int)
    ensures !(4 < z * z && z * z < 8)
{
    if z >= -2 && z <= 2 {
        // |z| <= 2 implies z*z <= 4
        assert(z * z <= 4);
        assert(!(4 < z * z && z * z < 8));
    } else {
        // |z| >= 3 implies z*z >= 9
        if z >= 3 {
            assert(9 <= z * z);
        } else {
            // z <= -3
            assert(-z >= 3);
            assert(9 <= z * z);
        }
        assert(!(4 < z * z && z * z < 8));
    }
}
// </vc-helpers>

// <vc-spec>
fn q(x: u32, y: u32) -> (z: u32)
    requires y - x > 2
    ensures x < z*z < y

fn strange()
    ensures 1 == 2
// </vc-spec>
// <vc-code>
{
    let x: u32 = 4;
    let c = q(x, 2 * x);
    proof {
        let c_i: int = c as int;
        let x_i: int = x as int;
        // x was initialized to 4
        assert(x_i == 4);
        // From the postcondition of q (in u32, cast to int)
        assert(x_i < c_i * c_i && c_i * c_i < 2 * x_i);
        // From x_i == 4 derive numeric bounds 4 < c_i*c_i < 8
        assert(4 < c_i * c_i);
        assert(c_i * c_i < 8);
        // Use the helper to rule out an integer square strictly between 4 and 8
        no_square_between_4_8(c_i);
        // Helper gives !(4 < c_i*c_i && c_i*c_i < 8), contradiction with the above
        assert(!(4 < c_i * c_i && c_i * c_i < 8));
        // Contradiction yields false, from which any postcondition follows
        assert(false);
        assert(1 == 2);
    }
}
// </vc-code>

fn main() {}

}