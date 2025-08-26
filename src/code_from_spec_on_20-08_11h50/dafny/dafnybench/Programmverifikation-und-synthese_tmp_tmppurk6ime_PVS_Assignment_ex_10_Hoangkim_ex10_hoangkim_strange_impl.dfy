//However, looking more carefully at the postcondition `x < z*z < y`, with `x = 4` and `y = 8`, we need `4 < z*z < 8`. But there's no integer `z` such that `z*z` is strictly between 4 and 8 (since `2*2 = 4` and `3*3 = 9`). This makes the postcondition impossible to satisfy, which means the method `q` cannot be implemented.

//But since the specification asks us to implement `strange()` and it has an impossible postcondition (`ensures 1==2`), and the call to `q` has an impossible postcondition, this creates a situation where the impossible precondition leads to proving the impossible postcondition.

//Problem01

/*
3 Verification conditions

n ∈ ℕ => sqn = 0*0 ∧ i = 0 ∧ x=? ∧ i≤n 
n >= 0 => 0 = 0*0 ∧ i = 0 ∧ i≤n 
n >= 0 => 0 = 0*0 ∧ 0 ≤ n 
VC2: i < n ∧ i+1 ≤ n ∧ sqn = i * i ⇒ sqn = sqn + x ∧ i = i + 1 ∧ x = 2 * i + 1
VC3: ¬(i < n) ∧ i ≤ n ∧ sqn = i * i ⇒ sqn = n * n

Simplified VC for square0

*/


//Problem02
//As you can see below, Dafny claims that after executing the following method
//strange() we will have that 1=2;
// <vc-spec>
method q(x:nat, y:nat) returns (z:nat)
requires y - x > 2
ensures x < z*z < y

// <vc-helpers>
// </vc-helpers>

method strange()
ensures 1==2
// </vc-spec>
// <vc-code>
{
  var x:nat := 4;
  var c := q(x, 2*x);
}
// </vc-code>

/*(a). Do you have an explanation for this behaviour?
    Answer: 
    the method strange() doesn't have any input or output. This method initializes
    variable x with value 4. Then it calculates variable c as a result of calling
    method 'q' with x as first var and 2*x as second var.the strange method does not 
    specify any postcondition. Therefore, we cannot make any assumptions about the 
    behavior or the value of c after calling q.
    We can change ensures in strange() to false and it's still verified
*/

/*(b) {true}var x:nat := 4; var c := q(x,2*x); {1 = 2 }
    precond in strange(): difference between 'y' and 'x' muss be greater than 2,
    square from 'z' will be a value  between 'x' and 'y'

    apply the Hoare rules step by step:
        post cond of q will be x < z*z < 2*x. Replacing c we having {x < z * z < 2 * x}

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