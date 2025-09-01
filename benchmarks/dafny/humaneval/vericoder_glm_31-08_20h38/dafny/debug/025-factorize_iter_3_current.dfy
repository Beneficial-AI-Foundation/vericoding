function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
lemma prod_append(s: seq<int>, t: seq<int>)
  ensures prod(s + t) == prod(s) * prod(t)
{
  if |s| == 0 {
    calc {
      prod(s + t);
      prod(t);
      1 * prod(t);
      prod(s) * prod(t);
    }
  } else {
    calc {
      prod(s + t);
      prod(s[..|s|-1] + [s[|s|-1]] + t);
      { prod_append(s[..|s|-1], [s[|s|-1]] + t); }
      prod(s[..|s|-1]) * prod([s[|s|-1]] + t);
      { assert prod([s[|s|-1]] + t) == s[|s|-1] * prod(t); }
      prod(s[..|s|-1]) * (s[|s|-1] * prod(t));
      (prod(s[..|s|-1]) * s[|s|-1]) * prod(t);
      prod(s) * prod(t);
    }
  }
}

lemma prod_singleton(x: int)
  ensures prod([x]) == x
{
  calc {
    prod([x]);
    prod([]) * x;
    1 * x;
    x;
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
  if n == 1 {
    return [];
  }
  var i := 2;
  while i * i <= n
    invariant 2 <= i <= n
    invariant n > 0
  {
    if n % i == 0 {
      var rest := factorize(n / i);
      return [i] + rest;
    }
    i := i + 1;
  }
  return [n];
}
// </vc-code>

