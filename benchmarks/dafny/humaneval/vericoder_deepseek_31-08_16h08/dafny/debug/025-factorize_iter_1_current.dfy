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
  } else {
    product_lemma(s[..|s|-1], i-1);
    assert prod(s) == prod(s[..|s|-1]) * s[|s|-1];
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
  }
}
// </vc-code>

