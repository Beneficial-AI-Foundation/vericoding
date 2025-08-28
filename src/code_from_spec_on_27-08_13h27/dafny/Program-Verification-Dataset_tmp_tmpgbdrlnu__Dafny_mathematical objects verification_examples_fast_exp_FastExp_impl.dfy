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
lemma BitsFromBitsCorrespondence(s: seq<bool>)
  ensures from_bits(s) == sum(s, |s|)
{
  if s == [] {
    assert from_bits(s) == 0;
    assert sum(s, |s|) == 0;
  } else {
    calc {
      from_bits(s);
      == (if s[0] then 1 else 0) + 2 * from_bits(s[1..]);
      { BitsFromBitsCorrespondence(s[1..]); }
      == (if s[0] then 1 else 0) + 2 * sum(s[1..], |s[1..]|);
      == sum(s, |s|);
    }
  }
}

lemma BitsProperty(n: nat)
  ensures from_bits(bits(n)) == n
{
  if n == 0 {
    assert bits(n) == [];
    assert from_bits([]) == 0;
  } else {
    calc {
      from_bits(bits(n));
      == from_bits([if (n % 2 == 0) then false else true] + bits(n/2));
      == (if (n % 2 == 0) then 0 else 1) + 2 * from_bits(bits(n/2));
      { BitsProperty(n/2); }
      == (if (n % 2 == 0) then 0 else 1) + 2 * (n / 2);
      == n % 2 + 2 * (n / 2);
      == n;
    }
  }
}

lemma SumSplit(s: seq<bool>, i: nat)
  requires 0 <= i <= |s|
  ensures sum(s, |s|) == sum(s[..i], i) + sum(s[i..], |s| - i)
{
  if i == 0 {
    assert s[..0] == [];
    assert sum([], 0) == 0;
    assert s[0..] == s;
    assert sum(s, |s|) == sum(s, |s|) + 0;
  } else if i == |s| {
    assert s[..i] == s;
    assert s[i..] == [];
    assert sum([], 0) == 0;
    assert sum(s, |s|) == sum(s, |s|) + 0;
  } else {
    calc {
      sum(s, |s|);
      == sum(s, i) + sum(s[i..], |s| - i);
    }
  }
}

lemma ExpProperty(b: nat, n1: nat, n2: nat)
  ensures exp(b, n1 + n2) == exp(b, n1) * exp(b, n2)
{
  if n2 == 0 {
    assert exp(b, n1 + 0) == exp(b, n1);
    assert exp(b, 0) == 1;
    assert exp(b, n1) * 1 == exp(b, n1);
  } else {
    calc {
      exp(b, n1 + n2);
      == exp(b, (n1 + n2) - 1 + 1);
      == b * exp(b, (n1 + n2) - 1);
      { ExpProperty(b, n1, n2 - 1); }
      == b * exp(b, n1) * exp(b, n2 - 1);
      == exp(b, n1) * (b * exp(b, n2 - 1));
      == exp(b, n1) * exp(b, n2);
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FastExp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method FastExp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
{
  var bits_n := bits(n);
  r := 1;
  var base := b;
  var i := 0;
  while i < |bits_n|
    invariant 0 <= i <= |bits_n|
    invariant r * exp(base, sum(bits_n[i..], |bits_n| - i)) == exp(b, n)
  {
    if bits_n[i] {
      r := r * base;
    }
    base := base * base;
    i := i + 1;
  }
}
// </vc-code>
