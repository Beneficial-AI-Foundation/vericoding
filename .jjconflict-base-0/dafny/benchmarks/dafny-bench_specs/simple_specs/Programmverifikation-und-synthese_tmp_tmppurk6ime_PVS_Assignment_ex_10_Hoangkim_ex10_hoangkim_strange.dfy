//ATOM

//Problem02
//As you can see below, Dafny claims that after executing the following method
//strange() we will have that 1=2;
method q(x:nat, y:nat) returns (z:nat)
requires y - x > 2
ensures x < z*z < y


// SPEC

method strange()
ensures 1==2
{
}
/*(a). Do you have an explanation for this behaviour?
  Answer: 
  the method strange() doesn't have any input or output. This method initializes
  variable x with value 4. Then it calculates variable c as a result of calling
