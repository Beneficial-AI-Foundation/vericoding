/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
// ATOM 

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}


// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
// ATOM 

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}
Iter

// Recursive version, imperative, with time and space complexity O(log n).
// SPEC 

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
{
}


// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.
//ATOM_PLACEHOLDER_unknown_1485 distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{
  //    
  // To use the proof below, deactivate automatic induction, with {:induction false}.
   /* if a == 0 {
        // base case
        calc == {
            power(x, a) * power(x, b);
            power(x, 0) * power(x, b); // substitution
            1.0 * power(x, b); // by the definition of power
            power(x, b); // neutral element of "*"
            power(x, a + b); // neutral element of "+"
        }
    }
    else {
        // recursive case, assuming property holds for a-1 (proof by induction)
        distributiveProperty(x, a-1, b); 
        // now do the proof
        calc == {
            power(x, a) * power(x, b);
            (x * power(x, a-1)) * power(x, b); // by the definition of power
            x * (power(x, a-1) * power(x, b)); // associative property
            x * power(x, a + b - 1); // this same property for a-1
            power(x, a + b); // definition of power
        }
    }*/
}

// A simple test case to make sure the specification is adequate.
//ATOM_PLACEHOLDER_testPowerIter

// SPEC 

method testPowerOpt(){
}


