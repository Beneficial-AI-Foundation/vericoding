function IsPrime(n: int) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
lemma IsPrimeImpliesNoDivisors(n: int)
  requires n > 1
  requires forall k :: 2 <= k < n ==> n % k != 0
  ensures IsPrime(n)
{
}

lemma NotIsPrimeImpliesDivisorExists(n: int)
  requires n > 1
  requires !IsPrime(n)
  ensures exists k :: 2 <= k < n && n % k == 0
{
}
// </vc-helpers>

// <vc-spec>
method PrimeLength(s: string) returns (p : bool)
  // post-conditions-start
  ensures p <==> IsPrime(|s|)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var len := |s|;
  
  if len <= 1 {
    p := false;
  } else {
    var i := 2;
    p := true;
    
    while i < len
      invariant 2 <= i <= len
      invariant p <==> (forall k :: 2 <= k < i ==> len % k != 0)
    {
      if len % i == 0 {
        p := false;
      }
      i := i + 1;
    }
    
    assert p <==> (forall k :: 2 <= k < len ==> len % k != 0);
  }
}
// </vc-code>

