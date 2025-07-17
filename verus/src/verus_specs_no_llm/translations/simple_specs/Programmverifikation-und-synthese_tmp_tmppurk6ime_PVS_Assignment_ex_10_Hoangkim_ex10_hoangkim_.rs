// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_q(x: nat, y: nat) -> z:nat)
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

/*(b
    requires
        y - x > 2
    ensures
        x < z*z < y


//ATOM

method strange(),
        1==2,
        in strange() to false && it's still verified
*/

/*(b)
;

proof fn lemma_q(x: nat, y: nat) -> (z: nat)
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

/*(b)
    requires
        y - x > 2
    ensures
        x < z*z < y


//ATOM

method strange(),
        1==2,
        in strange() to false && it's still verified
*/

/*(b)
{
    (0, 0)
}

}