function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
lemma product_lemma(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures prod(s) == prod(s[..i]) * prod(s[i..])
  decreases |s|
{
  if |s| == 0 {
    // Base case: empty sequence
  } else if i == 0 {
    // Trivial case: left part is empty
    assert s[0..] == s;
    assert prod(s) == prod(s[..0]) * prod(s[0..]);
  } else if i == |s| {
    // Trivial case: right part is empty
    assert s[..|s|] == s;
    assert prod(s) == prod(s[..|s|]) * prod(s[|s|..]);
  } else {
    // Recursive case: split at i
    var s_prefix := s[..|s|-1];
    product_lemma(s_prefix, i);
    
    calc == {
      prod(s);
      prod(s_prefix) * s[|s|-1];
      prod(s_prefix[..i]) * prod(s_prefix[i..]) * s[|s|-1];
      prod(s[..i]) * (prod(s_prefix[i..]) * s[|s|-1]);
      { 
        assert s_prefix[i..] == s[i..|s|-1];
        assert s[i..] == s[i..|s|-1] + [s[|s|-1]];
        product_concat_lemma(s_prefix[i..], [s[|s|-1]]);
        assert prod(s_prefix[i..]) * s[|s|-1] == prod(s[i..]);
      }
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
  decreases |s1|
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
    assert prod([]) == 1;
  } else {
    var s1_prefix := s1[..|s1|-1];
    var last_elem := s1[|s1|-1];
    
    // First prove the associative property of concatenation
    calc == {
      (s1_prefix + [last_elem]) + s2;
      s1_prefix + ([last_elem] + s2);
    }
    
    calc == {
      prod(s1 + s2);
      prod(s1_prefix + [last_elem] + s2);
      prod(s1_prefix + ([last_elem] + s2));
      { product_concat_lemma(s1_prefix, [last_elem] + s2); }
      prod(s1_prefix) * prod([last_elem] + s2);
      { product_concat_lemma([last_elem], s2); }
      prod(s1_prefix) * (prod([last_elem]) * prod(s2));
      prod(s1_prefix) * last_elem * prod(s2);
      { assert prod(s1) == prod(s1_prefix) * last_elem; }
      prod(s1) * prod(s2);
    }
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
    while d <= n && n % d != 0
      invariant 2 <= d <= n + 1
      decreases n - d
    {
      d := d + 1;
    }
    // d is guaranteed to be a divisor of n since we found the first divisor
    assert n % d == 0 && d <= n;
    var rest_factors := factorize(n / d);
    factors := rest_factors + [d];
    product_concat_lemma(rest_factors, [d]);
  }
}
// </vc-code>

