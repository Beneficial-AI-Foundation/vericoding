//ATOM
method max_nit(b: nat) returns (nmax : nat)
 requires (valid_base(b))
 ensures (nitness(b, nmax))
 ensures (is_max_nit(b, nmax))
{
  nmax := 0;
  assume (nitness(b, nmax));
  assume (is_max_nit(b, nmax));
  return nmax;
}

/*
 Now we define the flip operation proper. For this to work,
 we need is_max_nit and a kind of silly proof to make Dafny
 happy.
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
predicate is_max_nit(b : nat, q : nat) {
 q == b - 1
}

/*
 Next we define a meta-operator (on a base b) that
 returns the max nit. To make Dafny (and our inner
 mathmatician) happy, we need to require that b is
 a valid base, and explicitly say max_nit(b) is
 a nit of b, and that max_nit(b) is_max_nit(b).
 I found these made the actual flip operation provable.
*/


// SPEC
method nit_flip(b: nat, n : nat) returns (nf : nat)
 requires (valid_base(b))
 requires (nitness(b, n))
 ensures (nitness (b, nf))
{
}

/*
 We will now take a detour back to addition. We want to define
 a general version of nit_increment that allows you to add any two nits
*/
