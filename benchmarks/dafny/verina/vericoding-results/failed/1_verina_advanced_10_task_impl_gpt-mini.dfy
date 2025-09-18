// <vc-preamble>
function pow(base: int, exp: nat): int
{
    if exp == 0 then 1 else base * pow(base, exp - 1)
}

predicate IsPrime(n: nat)
{
    true // Abstract predicate for prime numbers
}

function SpecFold(pairs: seq<(nat, nat)>, acc: int): int
    decreases |pairs|
{
    if |pairs| == 0 then
        acc
    else
        var p, e := pairs[0].0, pairs[0].1;
        SpecFold(pairs[1..], acc * pow(p as int, e))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): pow multiplication lemma */
lemma PowMulSucc(base: int, e: nat)
  ensures pow(base, e+1) == base * pow(base, e)
  decreases e
{
  if e == 0 {
    // pow(base,1) == base * pow(base,0) by definition
  } else {
    PowMulSucc(base, e-1);
  }
}

/* helper modified by LLM (iteration 5): SpecFold append lemma */
lemma SpecFoldAppend(pairs: seq<(nat, nat)>, p: nat, e: nat, acc: int)
  ensures SpecFold(pairs + [(p, e)], acc) == SpecFold(pairs, acc) * pow(p as int, e)
  decreases |pairs|
{
  if |pairs| == 0 {
    assert SpecFold([], acc) == acc;
    assert SpecFold([(p, e)], acc) == SpecFold([], acc * pow(p as int, e));
    assert SpecFold([], acc * pow(p as int, e)) == acc * pow(p as int, e);
    assert SpecFold([], acc) * pow(p as int, e) == acc * pow(p as int, e);
  } else {
    var q := pairs[0].0; var f := pairs[0].1;
    // Sequence indexing/slicing facts
    assert (pairs + [(p, e)])[0] == pairs[0];
    assert (pairs + [(p, e)])[1..] == pairs[1..] + [(p, e)];
    // Unfold SpecFold on both sides
    assert SpecFold(pairs + [(p, e)], acc) == SpecFold(pairs[1..] + [(p, e)], acc * pow(q as int, f));
    assert SpecFold(pairs, acc) == SpecFold(pairs[1..], acc * pow(q as int, f));
    // Apply induction hypothesis to tail
    SpecFoldAppend(pairs[1..], p, e, acc * pow(q as int, f));
    // Use IH result to complete the step
    assert SpecFold(pairs[1..] + [(p, e)], acc * pow(q as int, f)) == SpecFold(pairs[1..], acc * pow(q as int, f)) * pow(p as int, e);
    assert SpecFold(pairs + [(p, e)], acc) == SpecFold(pairs, acc) * pow(p as int, e);
  }
}

/* helper modified by LLM (iteration 5): division exactness */
lemma DivExact(a: nat, b: nat)
  requires b > 0
  requires a % b == 0
  ensures a / b * b == a
{
  assert a == (a / b) * b + a % b;
  assert a % b == 0;
  assert a == (a / b) * b;
}

// </vc-helpers>

// <vc-spec>
method FindExponents(n: nat, primes: seq<nat>) returns (result: seq<(nat, nat)>)
    requires forall i :: 0 <= i < |primes| ==> IsPrime(primes[i])
    ensures n as int == SpecFold(result, 1)
    ensures forall i :: 0 <= i < |result| ==> result[i].0 in primes
    ensures forall p :: p in primes ==> 
        exists j :: 0 <= j < |result| && result[j].0 == p
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): factor n over given primes with invariants and proofs */
  var res: seq<(nat, nat)> := [];
  var rem := n;
  var i := 0;
  while i < |primes|
    decreases |primes| - i
    invariant 0 <= i <= |primes|
    invariant |res| == i
    invariant forall j :: 0 <= j < |res| ==> res[j].0 == primes[j]
    invariant SpecFold(res, 1) * (rem as int) == n as int
  {
    var p := primes[i];
    var e := 0;
    if p <= 1 {
      var prev := res;
      // append (p,0) while preserving SpecFold invariant
      SpecFoldAppend(prev, p, e, 1);
      assert SpecFold(prev + [(p, e)], 1) == SpecFold(prev, 1) * pow(p as int, e);
      res := prev + [(p, e)];
      // SpecFold(res,1) * rem == n holds from outer invariant and pow(...,0)==1
      i := i + 1;
      continue;
    }
    while rem != 0 && rem % p == 0
      decreases rem
      invariant 0 <= e
      invariant |res| == i
      invariant forall j :: 0 <= j < |res| ==> res[j].0 == primes[j]
      invariant SpecFold(res, 1) * (rem as int) * pow(p as int, e) == n as int
    {
      var oldRem := rem;
      var oldE := e;
      rem := rem / p;
      e := e + 1;
      DivExact(oldRem, p);
      PowMulSucc(p as int, oldE);
      // prove updated inner invariant
      assert pow(p as int, e) == p as int * pow(p as int, oldE);
      assert oldRem == (oldRem / p) * p;
      assert (rem as int) * pow(p as int, e) == (oldRem / p) * (p as int * pow(p as int, oldE));
      assert (oldRem / p) * (p as int * pow(p as int, oldE)) == oldRem * pow(p as int, oldE);
      assert SpecFold(res, 1) * (rem as int) * pow(p as int, e) == SpecFold(res, 1) * oldRem * pow(p as int, oldE);
      assert SpecFold(res, 1) * oldRem * pow(p as int, oldE) == n as int;
    }
    var prev2 := res;
    SpecFoldAppend(prev2, p, e, 1);
    assert SpecFold(prev2 + [(p, e)], 1) == SpecFold(prev2, 1) * pow(p as int, e);
    res := prev2 + [(p, e)];
    // Now SpecFold(res,1) * rem == n follows from the inner invariant
    assert SpecFold(res, 1) * (rem as int) == n as int;
    i := i + 1;
  }
  result := res;
}

// </vc-code>
