//ATOM

//Problem02
//As you can see below, Dafny claims that after executing the following method
//strange() we will have that 1=2;
method q(x:nat, y:nat) returns (z:nat)
requires y - x > 2
ensures x < z*z < y

//ATOM

method strange()
ensures 1==2
{
  assume 1==2;
}
/*(a). Do you have an explanation for this behaviour?
  Answer: 
  the method strange() doesn't have any input or output. This method initializes
  variable x with value 4. Then it calculates variable c as a result of calling


// SPEC
  method 'q' with x as first var and 2*x as second var.the strange method does not 
  specify any postcondition. Therefore, we cannot make any assumptions about the 
  behavior or the value of c after calling q.
  We can change ensures in strange() to false and it's still verified
*/

/*(b) {
}
  precond in strange(): difference between 'y' and 'x' muss be greater than 2,
  square from 'z' will be a value between 'x' and 'y'

  apply the Hoare rules step by step:
  1. {
}
  2. we assign 4 to 'x' and having {
}
  3. assign value q(x, 2 * x) to c, substitute the postcondition of 'q' in place of 'c'
    post cond of q will be x < z*z < 2*x. Replacing c we having {
}
  4. we having the statement {
}

  as we know the statment {
}



*/