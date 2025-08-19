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


//IMPL nit_increment
method nit_increment(b : nat, n : nat) returns (sum : nat, carry : nat)
 // Note: apparently, you need to explicitly put this here
 // even though we've got it in the nitness predicate
 requires (valid_base(b))
 requires (nitness(b, n))
 ensures (nitness(b, sum))
 ensures (nitness(b, carry))
{
 var incremented := n + 1;
 sum := incremented % b;
 carry := incremented / b;
}

/*
 Okay next we are going to define the flip operation. In binary,
 flip(0) = 1 and flip(1) = 0. We can generalize it to any base
 by defining it as so:

 let q be the max possible value of a given base. This
 is b - 1. Given some nit n of b, the flip(n) is q - n.

 For base 2, q = b - 1 = 2 - 1 = 1. flip(0) = 1 - 0 = 1,
 and flip(1) = 1 - 1 = 0.

 For base 3, q = 3 - 1 = 2. flip(0) = 2 - 0 = 2,
 flip(1) = 2 - 1 = 1, and flip(2) = 2 - 2 = 0.

 To begin with, we define a predicate is_max_nit which
 is true if some natural q == b - 1.
*/