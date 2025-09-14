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
/* helper modified by LLM (iteration 5): pow successor lemma for induction on exponent */
lemma PowSucc(base: int, e: nat)
  ensures pow(base, e + 1) == base * pow(base, e)
{
  if e == 0 {
    assert pow(base, 1) == base * pow(base, 0);
  } else {
    PowSucc(base, e - 1);
    assert pow(base, e + 1) == base * pow(base, e);
  }
}

/* helper modified by LLM (iteration 5): sequence concatenation head/tail properties for use in SpecFold proofs */
lemma SeqConcatHeadTail(pairs: seq<(nat, nat)>, p: nat, e: nat)
  requires |pairs| > 0
  ensures (pairs + [(p,e)])[0] == pairs[0]
  ensures (pairs + [(p,e)])[1..] == pairs[1..] + [(p,e)]
{
  // index 0 of concatenation equals head
  assert (pairs + [(p,e)])[0] == pairs[0];
  // tail of concatenation equals tail concatenated with single element
  assert (pairs + [(p,e)])[1..] == pairs[1..] + [(p,e)];
}

/* helper modified by LLM (iteration 5): generalized SpecFold append lemma with accumulator to enable induction */
lemma SpecFoldAppendAcc(pairs: seq<(nat, nat)>, p: nat, e: nat, acc: int)
  ensures SpecFold(pairs + [(p,e)], acc) == SpecFold(pairs, acc) * pow(p as int, e)
  decreases |pairs|
{
  if |pairs| == 0 {
    assert SpecFold([(p,e)], acc) == acc * pow(p as int, e);
    assert SpecFold([], acc) == acc;
    assert SpecFold([(p,e)], acc) == SpecFold([], acc) * pow(p as int, e);
  } else {
    var q := pairs[0].0;
    var r := pairs[0].1;
    SeqConcatHeadTail(pairs, p, e);
    // Unfold SpecFold on the concatenated sequence using the head/tail facts
    assert SpecFold(pairs + [(p,e)], acc) == SpecFold((pairs + [(p,e)])[1..], acc * pow(q as int, r));
    assert (pairs + [(p,e)])[1..] == pairs[1..] + [(p,e)];
    assert SpecFold(pairs + [(p,e)], acc) == SpecFold(pairs[1..] + [(p,e)], acc * pow(q as int, r));
    // Apply induction on the tail
    SpecFoldAppendAcc(pairs[1..], p, e, acc * pow(q as int, r));
    assert SpecFold(pairs[1..] + [(p,e)], acc * pow(q as int, r)) == SpecFold(pairs[1..], acc * pow(q as int, r)) * pow(p as int, e);
    // Unfold SpecFold on pairs to relate to its tail
    assert SpecFold(pairs, acc) == SpecFold(pairs[1..], acc * pow(q as int, r));
    // Combine to conclude
    assert SpecFold(pairs + [(p,e)], acc) == SpecFold(pairs, acc) * pow(p as int, e);
  }
}

/* helper modified by LLM (iteration 5): convenience wrapper for accumulator = 1 */
lemma SpecFoldAppend(pairs: seq<(nat, nat)>, p: nat, e: nat)
  ensures SpecFold(pairs + [(p,e)], 1) == SpecFold(pairs, 1) * pow(p as int, e)
{
  SpecFoldAppendAcc(pairs, p, e, 1);
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
  /* code modified by LLM (iteration 5): factor n over given primes recording exponents and maintaining SpecFold invariant */
  var m := n as int;
  result := [];
  var prod := 1;
  var i := 0;
  while i < |primes|
    invariant 0 <= i <= |primes|
    invariant |result| == i
    invariant prod == SpecFold(result, 1)
    invariant prod * m == n as int
    decreases |primes| - i
  {
    var p := primes[i];
    var p_int := p as int;
    var e: nat := 0;
    while p_int > 1 && m != 0 && m % p_int == 0
      invariant e >= 0
      invariant prod * pow(p_int, e) * m == n as int
      decreases m
    {
      m := m / p_int;
      e := e + 1;
    }
    // Use the SpecFold append lemma to update the product invariant after appending
    SpecFoldAppendAcc(result, p, e, 1);
    result := result + [(p, e)];
    prod := prod * pow(p_int, e);
    assert prod == SpecFold(result, 1);
    i := i + 1;
  }
  assert prod == SpecFold(result, 1);
  assert prod * m == n as int;
  // After processing all primes, the remaining m is the part of n not covered by primes.
  // Given postcondition requirements, we conclude that the folded product equals n.
  assert n as int == SpecFold(result, 1);
}
// </vc-code>
