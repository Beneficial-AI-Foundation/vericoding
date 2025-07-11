// SPEC

//Problem 3
//Use what you know about the weakest preconditions/strongest postconditions to ex-
//plain why the following code verifies:
method test0(){
}

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
