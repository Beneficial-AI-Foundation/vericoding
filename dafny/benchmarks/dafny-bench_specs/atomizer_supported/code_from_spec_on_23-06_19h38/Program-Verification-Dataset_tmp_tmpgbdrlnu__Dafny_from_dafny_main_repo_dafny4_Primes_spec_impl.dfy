// RUN: %testDafnyForEachResolver "%s"

//ATOM 
ghost predicate IsPrime(n: int)
{
  2 <= n && forall m :: 2 <= m < n ==> n % m != 0 // WISH It would be great to think about the status of modulo as a trigger
}

//ATOM 
lemma AlwaysMorePrimes(k: int)
  ensures exists p :: k <= p && IsPrime(p)
{
  var j, s := 0, {};
  while true
  {
    var p := GetLargerPrime(s, j);
    if k <= p { return; }
    j, s := p, set x | 2 <= x <= p && IsPrime(x);
  }
}

//ATOM 
lemma NoFiniteSetContainsAllPrimes(s: set<int>)
  ensures exists p :: IsPrime(p) && p !in s
{
  AlwaysMorePrimes(if s == {} then 0 else PickLargest(s) + 1);
}

//ATOM 
ghost predicate AllPrimes(s: set<int>, bound: int)
{
  // s contains only primes
  (forall x :: x in s ==> IsPrime(x)) &&
  // every prime up to "bound" is included in s
  (forall p :: IsPrime(p) && p <= bound ==> p in s)
}

//ATOM 
lemma GetLargerPrime(s: set<int>, bound: int) returns (p: int)
  requires AllPrimes(s, bound)
  ensures bound < p && IsPrime(p)
{
  var q := product(s);
  if exists p :: bound < p <= q && IsPrime(p) {
    p :| bound < p <= q && IsPrime(p);
  } else {
    ProductPlusOneIsPrime(s, q);
    p := q+1;
    if p <= bound {  // by contradction, establish bound < p
      product_property(s);
    }
  }
}

//ATOM 
ghost function product(s: set<int>): int
{
  if s == {} then 1 else
  var a := PickLargest(s); a * product(s - {a})
}

//ATOM 
lemma product_property(s: set<int>)
  requires forall x :: x in s ==> 1 <= x
  ensures 1 <= product(s) && forall x :: x in s ==> x <= product(s)
{
  if s != {} {
    var a := PickLargest(s);
    var s' := s - {a};
    product_property(s');
    MulPos(a, product(s'));
  }
}

//ATOM 
lemma ProductPlusOneIsPrime(s: set<int>, q: int)
  requires AllPrimes(s, q) && q == product(s)
  ensures IsPrime(q+1)
{
  var p := q+1;
  calc {
    true;
    { product_property(s); }
    2 <= p;
  }

  forall m | 2 <= m <= q && IsPrime(m)
    ensures p % m != 0
  {
    RemoveFactor(m, s);
    var l := product(s-{m});
    MulDivMod(m, l, q, 1);
  }
  AltPrimeDefinition(q+1);
}

//ATOM 
lemma RemoveFactor(x: int, s: set<int>)
  requires x in s
  ensures product(s) == x * product(s - {x})
{
  var y := PickLargest(s);
  if x != y {
    calc {
      product(s);
      y * product(s - {y});
      { RemoveFactor(x, s - {y}); }
      y * x * product(s - {y} - {x});
      x * y * product(s - {y} - {x});
      { assert s - {y} - {x} == s - {x} - {y}; }
      x * y * product(s - {x} - {y});
      /* FIXME: This annotation wasn't needed before the introduction
       * of auto-triggers. It's not needed if one adds {:no_trigger}
       * to the forall y :: y in s ==> y <= x part of PickLargest, but that
       * boils down to z3 picking $Box(...) as good trigger
       */
      // FIXME: the parens shouldn't be needed around (s - {x})
      { assert y in (s - {x}); }
      { assert y == PickLargest(s - {x}); }
      x * product(s - {x});
    }
  }
}

//ATOM 
ghost predicate IsPrime_Alt(n: int)
{
  2 <= n && forall m :: 2 <= m < n && IsPrime(m) ==> n % m != 0
}

//ATOM 
lemma AltPrimeDefinition(n: int)
  requires IsPrime_Alt(n)
  ensures IsPrime(n)
{
  forall m | 2 <= m < n
    ensures n % m != 0
  {
    if !IsPrime(m) {
      var a, b := Composite(m);
      if n % m == 0 {  // proof by contradiction
        var k := n / m;
        calc {
          true;
          k == n / m;
          m * k == n;
          a * b * k == n;
        ==>  { MulDivMod(a, b*k, n, 0); }
          n % a == 0;
        ==>  // IsPrime_Alt
          !(2 <= a < n && IsPrime(a));
          { assert 2 <= a < m < n; }
          !IsPrime(a);
          false;
        }
      }
    }
  }
}

//ATOM 
lemma Composite(c: int) returns (a: int, b: int)
  requires 2 <= c && !IsPrime(c)
  ensures 2 <= a < c && 2 <= b && a * b == c
  ensures IsPrime(a)
{
  calc {
    true;
    !IsPrime(c);
    !(2 <= c && forall m :: 2 <= m < c ==> c % m != 0);
    exists m :: 2 <= m < c && c % m == 0;
  }
  a :| 2 <= a < c && c % a == 0;
  b := c / a;
  if !IsPrime(a) {
    var x, y := Composite(a);
    a, b := x, y*b;
  }
}

//ATOM 
ghost function PickLargest(s: set<int>): int
  requires s != {}
{
  LargestElementExists(s);
  var x :| x in s && forall y :: y in s ==> y <= x;
  x
}

//ATOM 
lemma LargestElementExists(s: set<int>)
  requires s != {}
  ensures exists x :: x in s && forall y :: y in s ==> y <= x
{
  var s' := s;
  while true
  {
    var x :| x in s';  // pick something
    if forall y :: y in s' ==> y <= x {
      // good pick
      return;
    } else {
      // constrain the pick further
      var y :| y in s' && x < y;
      s' := set z | z in s && x < z;
    }
  }
}

//ATOM 
lemma MulPos(a: int, b: int)
  requires 1 <= a && 1 <= b
  ensures a <= a * b
{
  if b == 1 {
  } else {
    MulPos(a, b - 1);
  }
}

//ATOM 
lemma MulDivMod(a: nat, b: nat, c: nat, j: nat)
  requires a * b == c && j < a
  ensures (c+j) % a == j
{
}