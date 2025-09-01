function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
lemma prod_append(s: seq<int>, x: int)
  ensures prod(s + [x]) == prod(s) * x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert prod([x]) == prod([]) * x;
  } else {
    var s' := s[..|s| - 1];
    var last := s[|s| - 1];
    assert s == s' + [last];
    assert s + [x] == s' + [last] + [x] == s' + [last, x];
    assert prod(s + [x]) == prod(s' + [last, x]);
    assert (s' + [last, x])[..|s' + [last, x]| - 1] == s' + [last];
    assert prod(s + [x]) == prod(s' + [last]) * x;
    assert prod(s' + [last]) == prod(s);
  }
}

lemma prod_positive(s: seq<nat>)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures prod(s) > 0
{
  if |s| == 0 {
    assert prod(s) == 1;
  } else {
    prod_positive(s[..|s| - 1]);
    assert prod(s) == prod(s[..|s| - 1]) * s[|s| - 1];
    assert prod(s[..|s| - 1]) > 0;
    assert s[|s| - 1] > 0;
    assert prod(s) > 0;
  }
}

lemma div_decreases(a: nat, b: nat)
  requires a > 0 && b > 1 && a % b == 0
  ensures a / b < a
{
  assert a >= b;
  assert a == (a / b) * b;
  assert a / b >= 1;
  
  if a / b >= a {
    assert a / b * b >= a * b;
    assert a >= a * b;
    assert 1 >= b;
    assert false;
  }
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
  var divisor := 2;
  
  while remaining > 1
    invariant remaining > 0
    invariant prod(factors) * remaining == n
    invariant divisor >= 2
    invariant forall i :: 0 <= i < |factors| ==> factors[i] >= 2
    invariant forall i :: 0 <= i < |factors| ==> factors[i] > 1
    invariant divisor <= remaining + 1
    decreases remaining
  {
    if remaining % divisor == 0 {
      factors := factors + [divisor];
      prod_append(factors[..|factors|-1], divisor);
      div_decreases(remaining, divisor);
      remaining := remaining / divisor;
      divisor := 2;
    } else {
      divisor := divisor + 1;
      if divisor * divisor > remaining {
        factors := factors + [remaining];
        prod_append(factors[..|factors|-1], remaining);
        remaining := 1;
      }
    }
  }
}
// </vc-code>

