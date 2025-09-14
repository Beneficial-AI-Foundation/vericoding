function sum(s: seq<int>, i: nat): int
    requires i <= |s|
{
    if i == 0 then 0 else sum(s, i-1) + s[i-1]
}

function exp(b: nat, n: nat): nat {
  if n == 0 then 1
  else b * exp(b, n-1)
}

function bits(n: nat): seq<bool>
  decreases n
{
  if n == 0 then []
  else [if (n % 2 == 0) then false else true] + bits(n/2)
}

function from_bits(s: seq<bool>): nat {
  if s == [] then 0
  else (if s[0] then 1 else 0) + 2 * from_bits(s[1..])
}

// <vc-helpers>
lemma ExpDouble(b: nat, k: nat)
  ensures exp(b, 2*k) == exp(b*b, k)
  decreases k
{
  if k == 0 {
    assert exp(b, 0) == 1;
    assert exp(b*b, 0) == 1;
  } else {
    // exp(b,2*k) = b * exp(b,2*k - 1)
    assert exp(b, 2*k) == b * exp(b, 2*k - 1);
    // exp(b,2*k - 1) = b * exp(b,2*k - 2)
    assert exp(b, 2*k - 1) == b * exp(b, 2*k - 2);
    assert exp(b, 2*k) == (b*b) * exp(b, 2*k - 2);
    assert 2*k - 2 == 2*(k-1);
    ExpDouble(b, k-1);
    assert exp(b, 2*(k-1)) == exp(b*b, k-1);
    assert (b*b) * exp(b*b, k-1) == exp(b*b, k);
    assert exp(b, 2*k) == exp(b*b, k);
  }
}
// </vc-helpers>

// <vc-spec>
method FastExp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
// </vc-spec>
// <vc-code>
{
  var res: nat := 1;
  var base: nat := b;
  var e: nat := n;
  while e > 0
    invariant res * exp(base, e) == exp(b, n)
    decreases e
  {
    if e % 2 == 1 {
      var oldRes := res;
      var oldE: nat := e;
      assert oldE > 0;
      res := res * base;
      e := oldE - 1;
      assert oldE == e + 1;
      assert exp(base, oldE) == base * exp(base, e);
      assert res * exp(base, e) == oldRes * exp(base, oldE);
    }
    if e > 0 {
      assert e % 2 == 0;
      var k: nat := e / 2;
      ExpDouble(base, k);
      base := base * base;
      e := k;
    }
  }
  r := res;
}
// </vc-code>

