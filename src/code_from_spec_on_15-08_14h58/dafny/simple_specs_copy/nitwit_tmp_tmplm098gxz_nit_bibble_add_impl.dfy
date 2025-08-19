method nit_add(b : nat, x : nat, y : nat) returns (z : nat, carry : nat)
 requires (valid_base(b))
 requires (nitness(b, x))
 requires (nitness(b, y))
 ensures (nitness(b, z))
 ensures (nitness(b, carry))
 // This is a useful fact for doing general form addition.
 ensures (carry == 0 || carry == 1)
{
  /* code modified by LLM (iteration 2): Fixed carry bounds proof by using proper assertions */
  var sum := x + y;
  z := sum % b;
  carry := sum / b;
  
  // Help Dafny prove that carry is 0 or 1
  assert x < b && y < b; // From nitness preconditions
  assert sum < 2 * b;    // Since x + y < b + b = 2*b
  assert carry == sum / b < 2 * b / b;  // Division property
  assert carry < 2;      // Therefore carry < 2
  assert carry >= 0;     // Division of nats is non-negative
  
  return z, carry;
}

/*
 It will come in handy to define a version of nit_add that takes
 an additional argument c. Suppose I wanted to do base 2 addition
 as follows:

  1 1
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
predicate nitness(b : nat, n : nat)
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
 is one set of ten items, and nothing left over". Or if I did 6 + 7,
 that is "one set of 10, and a set of 3".

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
















predicate valid_base(b : nat) {
 b >= 2
}

/*
 Now we are in a position to define a nit formally. We say
 a natural number n is a "nit" of some base b if 0 <= n < b.
 0 and 1 are 2-nits ("bits") since 0 <= 0 < 2 and 0 <= 1 < 2.
*/


//ATOM
method nit_add_three(b : nat, c : nat, x : nat, y : nat) returns (z : nat, carry : nat)
 requires (valid_base(b))
 requires (c == 0 || c == 1)
 requires (nitness(b, x))
 requires (nitness(b, y))
 ensures (nitness(b, z))
 ensures (nitness(b, carry))
 ensures (carry == 0 || carry == 1)
{
  /* code modified by LLM (iteration 1): Fixed compilation error by correcting implementation and removing invalid assume statements */
  var sum := c + x + y;
  z := sum % b;
  carry := sum / b;
  return z, carry;
}

/*
 Whereas in binary computers, where we've the byte,
 we will define a general version called a "nyte". A "nyte"
 would be a collection of eight nits. However, for
 simplicity's sake, we deal in half-nytes. A nibble is a
 half-byte, so in our program we will call it a bibble.

 So, a bibble given some valid_base b is a collection
 of four nits.
*/


//ATOM
predicate bibble(b : nat, a : seq<nat>)
{
 valid_base(b) && 
 |a| == 4 && 
 forall n :: n in a ==> nitness(b, n)
}

/*
 As with nits, we will define addition, increment, and flip operations.
*/


//IMPL bibble_add
method bibble_add(b : nat, p : seq<nat>, q : seq<nat>) returns (r : seq<nat>)
 requires (valid_base(b))
 requires (bibble(b, p))
 requires (bibble(b, q))
 ensures (bibble(b, r))
{
  /* code modified by LLM (iteration 1): Fixed compilation error by removing invalid text and implementing bibble addition using nit_add_three */
  var r0, carry0 := nit_add_three(b, 0, p[0], q[0]);
  var r1, carry1 := nit_add_three(b, carry0, p[1], q[1]);
  var r2, carry2 := nit_add_three(b, carry1, p[2], q[2]);
  var r3, carry3 := nit_add_three(b, carry2, p[3], q[3]);
  
  r := [r0, r1, r2, r3];
}