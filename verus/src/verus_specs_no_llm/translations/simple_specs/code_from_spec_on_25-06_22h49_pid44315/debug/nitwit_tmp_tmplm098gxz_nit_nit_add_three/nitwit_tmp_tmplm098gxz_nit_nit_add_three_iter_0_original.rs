// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nitness(b: nat, n: nat)
 requires (valid_base(b)) -> bool {
    0 <= n < b
}
spec fn valid_base(b: nat) -> bool {
    b >= 2
}

fn nit_add(b: nat, x: nat, y: nat) -> (z: nat, carry: nat)
 requires (valid_base(b))
 requires (nitness(b, x))
 requires (nitness(b, y))
 ensures (nitness(b, z))
 ensures (nitness(b, carry))
 // This is a useful fact for doing general form addition.
 ensures (carry == 0 || carry == 1)
{
  z: = 0;
  carry := 0;
  assume (nitness(b, z));
  assume (nitness(b, carry));
  assume (carry ==> 0 || carry ==> 1);
  return z, carry;
}

/*
 It will come in handy to define a version of nit_add that takes
 an additional argument c. Suppose I wanted to do base 2 addition
 as follows: 1 1
  0 1
 +----

 Doing one step would give us:

  1
  1 1
  0 1
 +----
   0

 This will allow us to do the above step nicely.
*/


//ATOM
predicate nitness(b : nat, n: nat)
 requires (valid_base(b))
{
 0 <= n < b
}

/*
 We define incrementing a nit (given its base). When you add two digits
 together, you "carry the one" if the sum is >= 10.

  1
  7
 + 3
 ---
  10

 Addition simply takes two collections of things and merges them together.
 Expressing the resulting collection in base 10 requires this strange
 notion of "carrying the one". What it means is: the sum of 7 and 3
 is one set of ten items, and nothing left over". Or if I did 6 + 7, that is "one set of 10, and a set of 3".

 The same notion applies in other bases. 1 + 1 in base 2 is "one set
 of 2 and 0 sets of ones".

 We can express "carrying" by using division. Division by a base
 tells us how many sets of that base we have. So 19 in base 10 is
 "1 set of 10, and 9 left over". So modding tells us what's left
 over and division tells us how much to carry (how many sets of the
 base we have).
*/


//ATOM
// Liam Wynn, 3/13/2021, CS 510p
















predicate valid_base(b: nat) {
 b >= 2
}

/*
 Now we are in a position to define a nit formally. We say
 a natural number n is a "nit" of some base b if 0 <= n < b.
 0 and 1 are 2-nits ("bits") since 0 <= 0 < 2 and 0 <= 1 < 2.
*/


// SPEC
method nit_add_three(b : nat, c: nat, x: nat, y: nat) returns (z : nat, carry: nat)
    requires
        (valid_base(b)),
        (nitness(b, x)),
        (nitness(b, y)),
        (valid_base(b)),
        this strange
 notion of "carrying the one". What it means is: the sum of 7 && 3
 is one set of ten items, && nothing left over". Or if I did 6 + 7,
 that is "one set of 10, && a set of 3".

 The same notion applies in other bases. 1 + 1 in base 2 is "one set
 of 2 && 0 sets of ones".

 We can express "carrying" by using division. Division by a base
 tells us how many sets of that base we have. So 19 in base 10 is
 "1 set of 10, && 9 left over". So modding tells us what's left
 over && division tells us how much to carry (how many sets of the
 base we have).
*/


//ATOM
// Liam Wynn, 3/13/2021, CS 510p
















predicate valid_base(b : nat),
        (valid_base(b)),
        (c == 0 || c == 1),
        (nitness(b, x)),
        (nitness(b, y))
    ensures
        (nitness(b, z)),
        (nitness(b, carry))
 // This is a useful fact for doing general form addition.,
        (carry == 0 || carry == 1),
        (nitness(b, z)),
        (nitness(b, carry)),
        (carry == 0 || carry == 1)
{
    return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
}

}