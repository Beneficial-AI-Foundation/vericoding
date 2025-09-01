function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
lemma product_lemma(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures prod(s) == prod(s[..i]) * prod(s[i..])
{
  if i == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
    assert prod([]) == 1;
  } else if i == |s| {
    assert s[..|s|] == s;
    assert s[|s|..] == [];
    assert prod([]) == 1;
  } else {
    product_lemma(s[..|s|-1], i);
    assert prod(s) == prod(s[..|s|-1]) * s[|s|-1];
    // Additional calculation to prove the final result
    calc == {
      prod(s);
      prod(s[..|s|-1]) * s[|s|-1];
      { product_lemma(s[..|s|-1], i); }
      prod(s[..i]) * prod(s[..|s|-1][i..]) * s[|s|-1];
      prod(s[..i]) * (prod(s[i..|s|-1]) * s[|s|-1]);
      prod(s[..i]) * prod(s[i..]);
    }
  }
}

lemma empty_product_is_one() 
  ensures prod([]) == 1 
{
}

lemma singleton_product(x: int) 
  ensures prod([x]) == x 
{
}

lemma product_concat_lemma(s1: seq<int>, s2: seq<int>)
  ensures prod(s1 + s2) == prod(s1) * prod(s2)
{
  if |s2| == 0 {
    assert s1 + [] == s1;
  } else {
    product_concat_lemma(s1, s2[..|s2|-1]);
    assert prod(s1 + s2) == prod(s1 + s2[..|s2|-1]) * s2[|s2|-1];
    assert prod(s1 + s2) == prod(s1) * prod(s2[..|s2|-1]) * s2[|s2|-1];
    assert prod(s1 + s2) == prod(s1) * prod(s2);
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
    factors := [];
  } else {
    var d := 2;
    while n % d != 0
      invariant d <= n
      decreases n - d
    {
      d := d + 1;
    }
    var rest_factors := factorize(n / d);
    factors := rest_factors + [d];
    product_concat_lemma(rest_factors, [d]);
    assert prod(factors) == prod(rest_factors) * d;
  }
}
// </vc-code>

