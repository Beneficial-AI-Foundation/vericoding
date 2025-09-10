predicate IsPowerOfTwo(n: int) 
    decreases n
{
    if n <= 0 then false
    else if n == 1 then true
    else if n % 2 == 1 then false
    else IsPowerOfTwo(n / 2)
}

predicate ValidInput(n: int) {
    n >= 1
}

predicate CorrectResult(n: int, result: int) {
    if n % 2 == 1 then 
        result == (n - 1) / 2
    else 
        exists z :: 1 <= z <= n && IsPowerOfTwo(z) && z <= n && z * 2 > n && result == (n - z) / 2
}

// <vc-helpers>
lemma Mul2PreservesPowerOfTwo(p: int)
    requires p >= 1
    requires IsPowerOfTwo(p)
    ensures IsPowerOfTwo(2 * p)
{
    // 2*p > 0
    assert 2 * p > 0;
    // 2*p is even
    assert (2 * p) % 2 == 0;
    // (2*p)/2 == p
    assert (2 * p) / 2 == p;
    // from the require we have IsPowerOfTwo(p), hence IsPowerOfTwo((2*p)/2)
    assert IsPowerOfTwo((2 * p) / 2);
    // By the definition of IsPowerOfTwo, the above facts imply IsPowerOfTwo(2*p)
    // (Dafny can conclude this from the asserted facts)
}

lemma OneIsPowerOfTwo()
    ensures IsPowerOfTwo(1)
{
    // Direct from the predicate definition: n == 1 => true
    assert IsPowerOfTwo(1);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures CorrectResult(n, result)
// </vc-spec>
// <vc-code>
{
  if n % 2 == 1 {
    result := (n - 1) / 2;
    return;
  }

  var p := 1;
  OneIsPowerOfTwo();
  while p * 2 <= n
    invariant 1 <= p <= n
    invariant IsPowerOfTwo(p)
    decreases n - p
  {
    var oldp := p;
    p := oldp * 2;
    Mul2PreservesPowerOfTwo(oldp);
  }

  // Now p is a power of two, 1 <= p <= n and p*2 > n
  result := (n - p) / 2;
}
// </vc-code>

