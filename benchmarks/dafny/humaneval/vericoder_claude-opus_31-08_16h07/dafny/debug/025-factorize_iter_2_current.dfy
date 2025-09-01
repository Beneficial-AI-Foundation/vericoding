function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
lemma prod_append(s: seq<int>, x: int)
  ensures prod(s + [x]) == prod(s) * x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert prod([x]) == x;
  } else {
    calc {
      prod(s + [x]);
      == prod((s + [x])[..|s + [x]| - 1]) * (s + [x])[|s + [x]| - 1];
      == prod(s) * x;
    }
  }
}

lemma prod_empty()
  ensures prod([]) == 1
{
}
// </vc-helpers>

// <vc-spec>
method factorize(n: nat) returns (factors: seq<nat>)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures prod(factors) == n
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  factors := [];
  var remaining := n;
  
  if n == 1 {
    factors := [];
    prod_empty();
    return;
  }
  
  while remaining > 1
    invariant remaining > 0
    invariant prod(factors) * remaining == n
  {
    var divisor := 2;
    
    while divisor <= remaining && remaining % divisor != 0
      invariant 2 <= divisor <= remaining + 1
    {
      divisor := divisor + 1;
    }
    
    if divisor <= remaining {
      factors := factors + [divisor];
      prod_append(factors[..|factors|-1], divisor);
      remaining := remaining / divisor;
    }
  }
  
  assert remaining == 1;
  assert prod(factors) * 1 == n;
  assert prod(factors) == n;
}
// </vc-code>

