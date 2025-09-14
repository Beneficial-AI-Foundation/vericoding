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
lemma ExpStep(b: nat, i: nat)
  ensures exp(b, i + 1) == b * exp(b, i)
{}
// </vc-helpers>

// <vc-spec>
method FastExp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
// </vc-spec>
// <vc-code>
{
  r := 1;
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant r == exp(b, i)
    decreases n - i
  {
    var j: nat := i;
    ExpStep(b, j);
    r := r * b;
    i := j + 1;
  }
}
// </vc-code>

