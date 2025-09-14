// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
lemma ExpEven(b: nat, k: nat)
  requires k % 2 == 0
  ensures exp(b, k) == exp(b*b, k/2)
  decreases k
{
  if k > 0 {
    assert k >= 2;
    ExpEven(b, k-2);
  }
}

lemma ExpOdd(b: nat, k: nat)
  requires k % 2 == 1
  ensures exp(b, k) == b * exp(b*b, k/2)
{
  assert k >= 1;
  ExpEven(b, k-1);
}
// </vc-helpers>

// <vc-spec>
method FastExp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
// </vc-spec>
// <vc-code>
{
  r := 1;
  var p := b;
  var k := n;
  while k > 0
    invariant r * exp(p, k) == exp(b, n)
    decreases k
  {
    if k % 2 == 1 {
      ExpOdd(p, k);
      r := r * p;
    } else {
      ExpEven(p, k);
    }
    p := p * p;
    k := k / 2;
  }
}
// </vc-code>
