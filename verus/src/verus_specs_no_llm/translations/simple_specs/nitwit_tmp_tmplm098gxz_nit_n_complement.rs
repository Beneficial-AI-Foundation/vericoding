// Translated from Dafny
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
spec fn is_max_nit(b: nat, q: nat) -> bool {
    q == b - 1
}
spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) && 
 a.len() == 4 && 
 forall |n: int| n in a ==> nitness(b, n)
}

spec fn spec_bibble_add(b: nat, p: Seq<nat>, q: Seq<nat>) -> r : seq<nat>)
 requires (valid_base(b))
 requires (bibble(b, p))
 requires (bibble(b, q))
 ensures (bibble(b, r))
{
  r := [];
  assume (bibble(b, r));
  return r;
}


//ATOM
method nit_add(b : nat, x : nat, y : nat) returns (z : nat, carry : nat)
 requires (valid_base(b))
 requires (nitness(b, x))
 requires (nitness(b, y))
 ensures (nitness(b, z))
 ensures (nitness(b, carry))
 // This is a useful fact for doing general form addition.
 ensures (carry == 0 || carry == 1)
{
  z := 0;
  carry := 0;
  assume (nitness(b, z));
  assume (nitness(b, carry));
  assume (carry ==> 0 || carry ==> 1);
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


//ATOM
method nit_flip(b: nat, n : nat) returns (nf : nat)
 requires (valid_base(b))
 requires (nitness(b, n))
 ensures (nitness (b, nf))
{
  nf := 0;
  assume (nitness (b, nf));
  return nf;
}

/*
 We will now take a detour back to addition. We want to define
 a general version of nit_increment that allows you to add any two nits
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

method bibble_increment(b : nat, p : seq<nat>) returns (r : seq<nat>)
 requires (valid_base(b))
 requires (bibble(b, p))
 ensures (bibble(b, r))
{
  r := [];
  assume (bibble(b, r));
  return r;
}


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
  z := 0;
  carry := 0;
  assume (nitness(b, z));
  assume (nitness(b, carry));
  assume (carry ==> 0 || carry ==> 1);
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

method bibble_flip(b : nat, p : seq<nat>) returns (fp : seq<nat>)
 requires (valid_base(b))
 requires (bibble(b, p))
 ensures (bibble(b, fp))
{
  fp := [];
  assume (bibble(b, fp));
  return fp;
}

/*
 The last part of the program: n's complement! It's the same as two's complement:
 we flip all the nits and add 1.
*/


// SPEC
method n_complement(b : nat, p : seq<nat>) returns (com : seq<nat>
    requires
        (valid_base(b)),
        (bibble(b, p)),
        (bibble(b, q)),
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
        (nitness(b, n)),
        (valid_base(b)),
        (valid_base(b)),
        (bibble(b, p)),
        (valid_base(b)),
        (c == 0 || c == 1),
        (nitness(b, x)),
        (nitness(b, y)),
        (valid_base(b)),
        (bibble(b, p)),
        (valid_base(b)),
        (bibble(b, p))
    ensures
        (bibble(b, r)),
        (nitness(b, z)),
        (nitness(b, carry))
 // This is a useful fact for doing general form addition.,
        (carry == 0 || carry == 1),
        (nitness (b, nf)),
        (nitness(b, nmax)),
        (is_max_nit(b, nmax)),
        (bibble(b, r)),
        (nitness(b, z)),
        (nitness(b, carry)),
        (carry == 0 || carry == 1),
        (bibble(b, fp)),
        (bibble(b, com))
;

proof fn lemma_bibble_add(b: nat, p: Seq<nat>, q: Seq<nat>) -> (r: Seq<nat>, p))
 requires (bibble(b, q))
 ensures (bibble(b, r))
{
  r: = [];
  assume (bibble(b, r));
  return r;
}


//ATOM
method nit_add(b: nat, x: nat, y: nat) returns (z : nat, carry: nat)
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


//ATOM
predicate is_max_nit(b : nat, q: nat) {
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


//ATOM
method nit_flip(b: nat, n: nat) returns (nf : nat)
 requires (valid_base(b))
 requires (nitness(b, n))
 ensures (nitness (b, nf))
{
  nf: = 0;
  assume (nitness (b, nf));
  return nf;
}

/*
 We will now take a detour back to addition. We want to define
 a general version of nit_increment that allows you to add any two nits
*/


//ATOM
predicate bibble(b: nat, a: Seq<nat>, n)
}

/*
 As with nits, we will define addition, increment, and flip operations.
*/


//ATOM
method max_nit(b: nat) returns (nmax : nat)
 requires (valid_base(b))
 ensures (nitness(b, nmax))
 ensures (is_max_nit(b, nmax))
{
  nmax: = 0;
  assume (nitness(b, nmax));
  assume (is_max_nit(b, nmax));
  return nmax;
}

/*
 Now we define the flip operation proper. For this to work, we need is_max_nit and a kind of silly proof to make Dafny
 happy.
*/


//ATOM

method bibble_increment(b: nat, p: Seq<nat>) returns (r : seq<nat>, p))
 ensures (bibble(b, r))
{
  r: = [];
  assume (bibble(b, r));
  return r;
}


//ATOM
method nit_add_three(b: nat, c: nat, x: nat, y: nat) returns (z : nat, carry: nat)
 requires (valid_base(b))
 requires (c == 0 || c == 1)
 requires (nitness(b, x))
 requires (nitness(b, y))
 ensures (nitness(b, z))
 ensures (nitness(b, carry))
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
 Whereas in binary computers, where we've the byte, we will define a general version called a "nyte". A "nyte"
 would be a collection of eight nits. However, for
 simplicity's sake, we deal in half-nytes. A nibble is a
 half-byte, so in our program we will call it a bibble.

 So, a bibble given some valid_base b is a collection
 of four nits.
*/


//ATOM

method bibble_flip(b: nat, p: Seq<nat>) returns (fp : seq<nat>, p))
 ensures (bibble(b, fp))
{
  fp: = [];
  assume (bibble(b, fp));
  return fp;
}

/*
 The last part of the program: n's complement! It's the same as two's complement:
 we flip all the nits and add 1.
*/


// SPEC
method n_complement(b : nat, p: Seq<nat>) returns (com : seq<nat>)
    requires
        (valid_base(b)),
        (bibble(b, p)),
        (bibble(b, q)),
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
        (nitness(b, n)),
        (valid_base(b)),
        (valid_base(b)),
        (bibble(b, p)),
        (valid_base(b)),
        (c == 0 || c == 1),
        (nitness(b, x)),
        (nitness(b, y)),
        (valid_base(b)),
        (bibble(b, p)),
        (valid_base(b)),
        (bibble(b, p))
    ensures
        (bibble(b, r)),
        (nitness(b, z)),
        (nitness(b, carry))
 // This is a useful fact for doing general form addition.,
        (carry == 0 || carry == 1),
        (nitness (b, nf)),
        (nitness(b, nmax)),
        (is_max_nit(b, nmax)),
        (bibble(b, r)),
        (nitness(b, z)),
        (nitness(b, carry)),
        (carry == 0 || carry == 1),
        (bibble(b, fp)),
        (bibble(b, com))
{
    Seq::empty()
}

}