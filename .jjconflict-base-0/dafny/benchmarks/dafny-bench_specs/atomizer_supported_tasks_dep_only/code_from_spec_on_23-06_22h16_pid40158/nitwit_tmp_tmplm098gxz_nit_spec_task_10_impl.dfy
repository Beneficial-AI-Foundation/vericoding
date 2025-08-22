// Liam Wynn, 3/13/2021, CS 510p

/*
  In this program, I'm hoping to define
  N's complement: a generalized form of 2's complement.

  I ran across this idea back in ECE 341, when I asked
  the professor about a crackpot theoretical "ternary machine".
  Looking into it, I came across a general form of 2's complement.

  Suppose I had the following 4 nit word in base base 3:

  1 2 0 1 (3)

  Now, in two's complement, you "flip" the bits and add 1. In
  n's complement, you flip the bits by subtracting the current
  nit value from the largest possible nit value. Since our base
  is 3, our highest possible nit value is 2:

  1 0 2 1 (3)

  Note how the 1's don't change (2 - 1 = 1), but the "flipping"
  is demonstrated in the 2 and 0. flip(2) in base 3 = 0, and flip(0)
  in base 3 = 2.

  Now let's increment our flipped word:

  1 0 2 2 (3)

  Now, if this is truly the n's complement of 1 2 0 1 (3), their
  sum should be 0:

    1 1 1
    1 2 0 1
  + 1 0 2 2
  ---------
  1 0 0 0 0 (3)

  Now, since our word size if 4 nits, the last nit gets dropped
  giving us 0 0 0 0!

  So basically I want to write a Dafny program that does the above
  but verified. I don't know how far I will get, but I essentially
  want to write an increment, addition, and flip procedures such
  that:

  sum(v, increment(flip(v)) = 0, where v is a 4 nit value in
  a given base n.

*/

/*
  In this program, we deal with bases that are explicitly greater
  than or equal to 2. Without this fact, virtually all of our
  postconditions will not be provable. We will run into issues
  of dividing by 0 and what not.
*/
//ATOM 
predicate valid_base(b : nat) {
  b >= 2
}

/*
  Now we are in a position to define a nit formally. We say
  a natural number n is a "nit" of some base b if 0 <= n < b.
  0 and 1 are 2-nits ("bits") since 0 <= 0 < 2 and 0 <= 1 < 2.
*/

//ATOM 
predicate nitness(b : nat, n : nat)
  requires (valid_base(b))
{
  0 <= n < b
}

//ATOM 
predicate is_max_nit(b : nat, q : nat) {
  q == b - 1
}

//IMPL max_nit
method max_nit(b: nat) returns (nmax : nat)
  requires (valid_base(b))
  ensures (nitness(b, nmax))
  ensures (is_max_nit(b, nmax))
{
  nmax := b - 1;
}

//IMPL nit_flip
method nit_flip(b: nat, n : nat) returns (nf : nat)
  requires (valid_base(b))
  requires (nitness(b, n))
  ensures (nitness (b, nf))
{
  var max_n := max_nit(b);
  nf := max_n - n;
}

//IMPL nit_add
method nit_add(b : nat, x : nat, y : nat) returns (z : nat, carry : nat)
  requires (valid_base(b))
  requires (nitness(b, x))
  requires (nitness(b, y))
  ensures  (nitness(b, z))
  ensures  (nitness(b, carry))
  // This is a useful fact for doing general form addition.
  ensures  (carry == 0 || carry == 1)
{
  var sum := x + y;
  z := sum % b;
  carry := sum / b;
}

//IMPL nit_add_three
method nit_add_three(b : nat, c : nat, x : nat, y : nat) returns (z : nat, carry : nat)
  requires (valid_base(b))
  requires (c == 0 || c == 1)
  requires (nitness(b, x))
  requires (nitness(b, y))
  ensures  (nitness(b, z))
  ensures  (nitness(b, carry))
  ensures  (carry == 0 || carry == 1)
{
  var sum := c + x + y;
  z := sum % b;
  carry := sum / b;
}

//ATOM 
predicate bibble(b : nat, a : seq<nat>)
{
  valid_base(b) && 
  |a| == 4 && 
  forall n :: n in a ==> nitness(b, n)
}

//IMPL bibble_add
method bibble_add(b : nat, p : seq<nat>, q : seq<nat>) returns (r : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  requires (bibble(b, q))
  ensures  (bibble(b, r))
{
  var r0, c0 := nit_add(b, p[3], q[3]);
  var r1, c1 := nit_add_three(b, c0, p[2], q[2]);
  var r2, c2 := nit_add_three(b, c1, p[1], q[1]);
  var r3, c3 := nit_add_three(b, c2, p[0], q[0]);
  r := [r3, r2, r1, r0];
}

//IMPL bibble_increment
method bibble_increment(b : nat, p : seq<nat>) returns (r : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  ensures  (bibble(b, r))
{
  var one := [0, 0, 0, 1];
  r := bibble_add(b, p, one);
}

//IMPL bibble_flip
method bibble_flip(b : nat, p : seq<nat>) returns (fp : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  ensures  (bibble(b, fp))
{
  var fp0 := nit_flip(b, p[0]);
  var fp1 := nit_flip(b, p[1]);
  var fp2 := nit_flip(b, p[2]);
  var fp3 := nit_flip(b, p[3]);
  fp := [fp0, fp1, fp2, fp3];
}

//IMPL n_complement
method n_complement(b : nat, p : seq<nat>) returns (com : seq<nat>)
  requires (valid_base(b))
  requires (bibble(b, p))
  ensures  (bibble(b, com))
{
  var flipped := bibble_flip(b, p);
  com := bibble_increment(b, flipped);
}

//IMPL Main
method Main() {
}