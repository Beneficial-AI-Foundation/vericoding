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
lemma from_bits_bound(s: seq<bool>)
  ensures from_bits(s) < exp(2, |s|)
{
  if s == [] {
  } else {
    from_bits_bound(s[1..]);
  }
}

lemma from_bits_append(s: seq<bool>, b: bool)
  ensures from_bits(s + [b]) == from_bits(s) + (if b then exp(2, |s|) else 0)
{
  if s == [] {
    assert s + [b] == [b];
  } else {
    calc {
      from_bits(s + [b]);
      == (if (s + [b])[0] then 1 else 0) + 2 * from_bits((s + [b])[1..]);
      == { assert (s + [b])[0] == s[0]; assert (s + [b])[1..] == s[1..] + [b]; }
      (if s[0] then 1 else 0) + 2 * from_bits(s[1..] + [b]);
      == { from_bits_append(s[1..], b); }
      (if s[0] then 1 else 0) + 2 * (from_bits(s[1..]) + (if b then exp(2, |s[1..]|) else 0));
      == (if s[0] then 1 else 0) + 2 * from_bits(s[1..]) + (if b then 2 * exp(2, |s|-1) else 0);
      == from_bits(s) + (if b then exp(2, |s|) else 0);
    }
  }
}

lemma bits_from_bits(n: nat)
  ensures from_bits(bits(n)) == n
{
  if n == 0 {
  } else {
    var b := if n % 2 == 0 then false else true;
    calc {
      from_bits(bits(n));
      == from_bits([b] + bits(n/2));
      == (if b then 1 else 0) + 2 * from_bits(bits(n/2));
      == { bits_from_bits(n/2); }
      (if b then 1 else 0) + 2 * (n/2);
      == { assert b <==> n % 2 == 1; }
      n % 2 + 2 * (n/2);
      == n;
    }
  }
}

lemma exp_sum(b: nat, x: nat, y: nat)
  ensures exp(b, x + y) == exp(b, x) * exp(b, y)
{
  if y == 0 {
    calc {
      exp(b, x + y);
      == exp(b, x + 0);
      == exp(b, x);
      == exp(b, x) * 1;
      == exp(b, x) * exp(b, 0);
      == exp(b, x) * exp(b, y);
    }
  } else {
    calc {
      exp(b, x + y);
      == b * exp(b, x + y - 1);
      == { exp_sum(b, x, y - 1); }
      b * exp(b, x) * exp(b, y - 1);
      == exp(b, x) * (b * exp(b, y - 1));
      == exp(b, x) * exp(b, y);
    }
  }
}

lemma exp_mul(b: nat, x: nat, y: nat)
  ensures exp(exp(b, x), y) == exp(b, x * y)
  decreases y
{
  if y == 0 {
    assert exp(exp(b, x), 0) == 1;
    assert exp(b, x * 0) == exp(b, 0) == 1;
  } else {
    calc {
      exp(exp(b, x), y);
      == exp(b, x) * exp(exp(b, x), y - 1);
      == { exp_mul(b, x, y - 1); }
      exp(b, x) * exp(b, x * (y - 1));
      == { exp_sum(b, x, x * (y - 1)); }
      exp(b, x + x * (y - 1));
      == { assert x + x * (y - 1) == x * (1 + (y - 1)) == x * y; }
      exp(b, x * y);
    }
  }
}

lemma exp_two_successor(i: nat)
  ensures exp(2, i + 1) == 2 * exp(2, i)
{
  calc {
    exp(2, i + 1);
    == 2 * exp(2, i);
  }
}
// </vc-helpers>

// <vc-spec>
method FastExp(b: nat, n: nat) returns (r: nat)
  ensures r == exp(b, n)
// </vc-spec>
// <vc-code>
{
  var bs := bits(n);
  var i := 0;
  var base := b;
  r := 1;
  
  while i < |bs|
    invariant 0 <= i <= |bs|
    invariant base == exp(b, exp(2, i))
    invariant r == exp(b, from_bits(bs[..i]))
  {
    var old_base := base;
    
    if bs[i] {
      // r == exp(b, from_bits(bs[..i]))
      // base == exp(b, exp(2, i))
      r := r * base;
      // r == exp(b, from_bits(bs[..i])) * exp(b, exp(2, i))
      exp_sum(b, from_bits(bs[..i]), exp(2, i));
      // r == exp(b, from_bits(bs[..i]) + exp(2, i))
    }
    
    assert bs[..i+1] == bs[..i] + [bs[i]];
    from_bits_append(bs[..i], bs[i]);
    // from_bits(bs[..i+1]) == from_bits(bs[..i]) + (if bs[i] then exp(2, i) else 0)
    
    if bs[i] {
      assert r == exp(b, from_bits(bs[..i]) + exp(2, i));
      assert r == exp(b, from_bits(bs[..i+1]));
    } else {
      assert r == exp(b, from_bits(bs[..i]));
      assert from_bits(bs[..i+1]) == from_bits(bs[..i]);
      assert r == exp(b, from_bits(bs[..i+1]));
    }
    
    base := base * base;
    i := i + 1;
    
    exp_two_successor(i - 1);
    assert exp(2, i) == 2 * exp(2, i - 1);
    exp_mul(b, exp(2, i - 1), 2);
    assert exp(exp(b, exp(2, i - 1)), 2) == exp(b, exp(2, i - 1) * 2);
    assert old_base * old_base == exp(b, exp(2, i - 1)) * exp(b, exp(2, i - 1));
    exp_sum(b, exp(2, i - 1), exp(2, i - 1));
    assert old_base * old_base == exp(b, 2 * exp(2, i - 1));
    assert base == exp(b, exp(2, i));
  }
  
  assert bs[..|bs|] == bs;
  bits_from_bits(n);
}
// </vc-code>

