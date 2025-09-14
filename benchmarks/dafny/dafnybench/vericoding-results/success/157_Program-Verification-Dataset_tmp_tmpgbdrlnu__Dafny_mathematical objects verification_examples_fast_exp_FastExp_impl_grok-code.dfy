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
lemma LemExpRecursive(x: nat, y: nat)
  decreases y
  requires y > 0
  ensures if y % 2 == 0 then exp(x, y) == exp(x * x, y / 2)
  else exp(x, y) == x * exp(x * x, (y - 1) / 2)
{
  if y % 2 == 0 {
    var z := y / 2;
    assert z > 0;
    LemExpRecursive(x, y-1);
    assert exp(x, y) == exp(x * x, z);
  } else {
    var z := (y - 1) / 2;
    if z == 0 {
      assert exp(x, y) == x * 1;
    } else {
      LemExpRecursive(x, y-1);
      assert exp(x, y) == x * exp(x * x, z);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method FastExp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
// </vc-spec>
// <vc-code>
{
  r := 1;
  var x := b;
  var y := n;
  while y > 0
    decreases y
    invariant r * exp(x, y) == exp(b, n)
  {
    LemExpRecursive(x, y);
    if y % 2 == 1 {
      r := r * x;
    }
    x := x * x;
    y := y / 2;
  }
}
// </vc-code>

