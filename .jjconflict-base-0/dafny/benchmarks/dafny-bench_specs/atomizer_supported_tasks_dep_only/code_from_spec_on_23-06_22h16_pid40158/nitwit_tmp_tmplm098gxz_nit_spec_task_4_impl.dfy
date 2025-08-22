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
// Liam Wynn, 3/13/2021, CS 510p

predicate valid_base(b : nat) {
  b >= 2
}

/*
  Now we are in a position to define a nit formally. We say
  a natural number n is a "nit" of some base b if 0 <= n < b.
  0 and 1 are 2-nits ("bits") since 0 <= 0 < 2 and 0 <= 1 < 2.
*/

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

/* code modified by LLM (iteration 1): Added missing helper functions and predicates with proper ensures clauses */
function nit_increment(b : nat, n : nat, carry_in : nat) : (nat, nat)
  requires valid_base(b)
  requires nitness(b, n)
  requires nitness(b, carry_in)
  ensures var (result, carry_out) := nit_increment(b, n, carry_in); nitness(b, result) && (carry_out == 0 || carry_out == 1)
{
  var sum := n + carry_in;
  (sum % b, sum / b)
}

predicate is_max_nit(b : nat, q : nat)
  requires valid_base(b)
{
  q == b - 1
}

function max_nit(b : nat) : nat
  requires valid_base(b)
  ensures nitness(b, max_nit(b))
  ensures is_max_nit(b, max_nit(b))
{
  b - 1
}

function nit_flip(b : nat, n : nat) : nat
  requires valid_base(b)
  requires nitness(b, n)
  ensures nitness(b, nit_flip(b, n))
{
  max_nit(b) - n
}

predicate valid_bibble(b : nat, bibble : seq<nat>)
  requires valid_base(b)
{
  |bibble| == 4 && forall i :: 0 <= i < |bibble| ==> nitness(b, bibble[i])
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
  /* code modified by LLM (iteration 1): Fixed implementation to satisfy postconditions with proper bounds checking */
  var sum := x + y;
  z := sum % b;
  carry := sum / b;
  
  // Help prove the carry property - since x < b and y < b, sum < 2*b, so carry < 2
  assert x < b && y < b;
  assert sum < 2 * b;
  assert carry == sum / b < 2;
  // Since carry is nat and carry < 2, carry must be 0 or 1
}

/* code modified by LLM (iteration 1): Added missing helper methods with proper verification */
method nit_add_three(b : nat, x : nat, y : nat, c : nat) returns (z : nat, carry : nat)
  requires valid_base(b)
  requires nitness(b, x)
  requires nitness(b, y)
  requires nitness(b, c)
  ensures nitness(b, z)
  ensures nitness(b, carry)
  ensures carry == 0 || carry == 1 || carry == 2
{
  var sum := x + y + c;
  z := sum % b;
  carry := sum / b;
  
  // Help prove the carry property - since x < b, y < b, c < b, sum < 3*b, so carry < 3
  assert x < b && y < b && c < b;
  assert sum < 3 * b;
  assert carry == sum / b < 3;
}

method bibble_add(b : nat, x : seq<nat>, y : seq<nat>) returns (z : seq<nat>)
  requires valid_base(b)
  requires valid_bibble(b, x)
  requires valid_bibble(b, y)
  ensures valid_bibble(b, z)
{
  z := [];
  var carry := 0;
  var i := 0;
  while i < 4
    invariant 0 <= i <= 4
    invariant |z| == i
    invariant carry == 0 || carry == 1
    invariant forall j :: 0 <= j < i ==> nitness(b, z[j])
  {
    var sum := x[i] + y[i] + carry;
    var digit := sum % b;
    var new_carry := sum / b;
    
    /* code modified by LLM (iteration 1): Proper carry handling with bounds verification */
    assert x[i] < b && y[i] < b && carry <= 1;
    assert sum < 2 * b + 1;
    assert new_carry <= 2;
    // For bibble arithmetic, we ignore overflow beyond the 4 nits
    if new_carry >= 2 {
      carry := 1;
    } else {
      carry := new_carry;
    }
    
    z := z + [digit];
    i := i + 1;
  }
}

method bibble_increment(b : nat, x : seq<nat>) returns (z : seq<nat>)
  requires valid_base(b)
  requires valid_bibble(b, x)
  ensures valid_bibble(b, z)
{
  z := [];
  var carry := 1;
  var i := 0;
  while i < 4
    invariant 0 <= i <= 4
    invariant |z| == i
    invariant carry == 0 || carry == 1
    invariant forall j :: 0 <= j < i ==> nitness(b, z[j])
  {
    var sum := x[i] + carry;
    var digit := sum % b;
    carry := sum / b;
    
    /* code modified by LLM (iteration 1): Add proper assertions for carry bounds */
    assert x[i] < b && carry <= 1;
    assert sum < b + 1;
    assert carry == sum / b;
    if sum < b {
      assert carry == 0;
    } else {
      assert sum == b;
      assert carry == 1;
    }
    
    z := z + [digit];
    i := i + 1;
  }
}

method bibble_flip(b : nat, x : seq<nat>) returns (z : seq<nat>)
  requires valid_base(b)
  requires valid_bibble(b, x)
  ensures valid_bibble(b, z)
{
  z := [];
  var i := 0;
  while i < 4
    invariant 0 <= i <= 4
    invariant |z| == i
    invariant forall j :: 0 <= j < i ==> nitness(b, z[j])
  {
    var flipped := nit_flip(b, x[i]);
    z := z + [flipped];
    i := i + 1;
  }
}

method n_complement(b : nat, x : seq<nat>) returns (z : seq<nat>)
  requires valid_base(b)
  requires valid_bibble(b, x)
  ensures valid_bibble(b, z)
{
  var flipped := bibble_flip(b, x);
  z := bibble_increment(b, flipped);
}

method Main()
{
  // Example usage with base 3
  var base := 3;
  var example : seq<nat> := [1, 2, 0, 1]; // represents 1201 in base 3
  
  /* code modified by LLM (iteration 1): Fixed conditional and added proper manual verification */
  if base >= 2 {
    // Manually verify bibble validity
    if |example| == 4 && 
       example[0] < base && example[1] < base && 
       example[2] < base && example[3] < base {
      var complement := n_complement(base, example);
      print "Original: ", example, "\n";
      print "N's complement: ", complement, "\n";
    }
  }
}