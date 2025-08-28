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
lemma BitsFromBitsIdentity(n: nat)
  ensures from_bits(bits(n)) == n
  decreases n
{
  if n == 0 {
    assert bits(0) == [];
    assert from_bits([]) == 0;
  } else {
    var b := bits(n);
    var rest := bits(n/2);
    assert b == [if (n % 2 == 0) then false else true] + rest;
    
    if n % 2 == 0 {
      assert b[0] == false;
      assert from_bits(b) == 0 + 2 * from_bits(rest);
      BitsFromBitsIdentity(n/2);
      assert from_bits(rest) == n/2;
      assert from_bits(b) == 2 * (n/2) == n;
    } else {
      assert b[0] == true;
      assert from_bits(b) == 1 + 2 * from_bits(rest);
      BitsFromBitsIdentity(n/2);
      assert from_bits(rest) == n/2;
      assert from_bits(b) == 1 + 2 * (n/2) == n;
    }
  }
}

lemma ExpSquareProperty(b: nat, n: nat)
  ensures exp(b, 2*n) == exp(exp(b, n), 2)
{
  if n == 0 {
    calc {
      exp(b, 2*0);
      == exp(b, 0);
      == 1;
      == 1 * 1;
      == exp(1, 2);
      == exp(exp(b, 0), 2);
    }
  } else {
    ExpSquareProperty(b, n-1);
    calc {
      exp(b, 2*n);
      == exp(b, 2 + 2*(n-1));
      == b * b * exp(b, 2*(n-1));
      == b * b * exp(exp(b, n-1), 2);
      == b * b * exp(b, n-1) * exp(b, n-1);
      == (b * exp(b, n-1)) * (b * exp(b, n-1));
      == exp(b, n) * exp(b, n);
      == exp(exp(b, n), 2);
    }
  }
}

lemma ExpAdditive(b: nat, m: nat, n: nat)
  ensures exp(b, m + n) == exp(b, m) * exp(b, n)
{
  if m == 0 {
    assert exp(b, 0 + n) == exp(b, n);
    assert exp(b, 0) * exp(b, n) == 1 * exp(b, n) == exp(b, n);
  } else {
    ExpAdditive(b, m-1, n);
    calc {
      exp(b, m + n);
      == b * exp(b, m + n - 1);
      == b * exp(b, (m-1) + n);
      == b * exp(b, m-1) * exp(b, n);
      == exp(b, m) * exp(b, n);
    }
  }
}

lemma ExpPower(b: nat, m: nat, n: nat)
  ensures exp(exp(b, m), n) == exp(b, m * n)
  decreases n
{
  if n == 0 {
    calc {
      exp(exp(b, m), 0);
      == 1;
      == exp(b, 0);
      == exp(b, m * 0);
    }
  } else {
    ExpPower(b, m, n-1);
    calc {
      exp(exp(b, m), n);
      == exp(b, m) * exp(exp(b, m), n-1);
      == exp(b, m) * exp(b, m * (n-1));
      == exp(b, m + m * (n-1));
      == exp(b, m * (1 + (n-1)));
      == exp(b, m * n);
    }
  }
}

lemma FromBitsBit(bits_n: seq<bool>, pos: nat)
  requires pos < |bits_n|
  ensures from_bits(bits_n[..pos+1]) == from_bits(bits_n[..pos]) + (if bits_n[pos] then exp(2, pos) else 0)
{
  if pos == 0 {
    if bits_n[0] {
      calc {
        from_bits(bits_n[..1]);
        == from_bits([bits_n[0]]);
        == 1 + 2 * from_bits([]);
        == 1 + 2 * 0;
        == 1;
        == from_bits([]) + exp(2, 0);
        == from_bits(bits_n[..0]) + exp(2, 0);
      }
    } else {
      calc {
        from_bits(bits_n[..1]);
        == from_bits([bits_n[0]]);
        == 0 + 2 * from_bits([]);
        == 0;
        == from_bits(bits_n[..0]) + 0;
      }
    }
  } else {
    FromBitsBit(bits_n[1..], pos-1);
    
    calc {
      bits_n[1..][..pos];
      == bits_n[1..pos+1];
    }
    
    if bits_n[pos] {
      calc {
        from_bits(bits_n[..pos+1]);
        == (if bits_n[0] then 1 else 0) + 2 * from_bits(bits_n[1..pos+1]);
        == (if bits_n[0] then 1 else 0) + 2 * from_bits(bits_n[1..][..pos]);
        == (if bits_n[0] then 1 else 0) + 2 * (from_bits(bits_n[1..][..pos-1]) + exp(2, pos-1));
        == (if bits_n[0] then 1 else 0) + 2 * from_bits(bits_n[1..pos]) + 2 * exp(2, pos-1);
        == from_bits(bits_n[..pos]) + exp(2, 1) * exp(2, pos-1);
        == from_bits(bits_n[..pos]) + exp(2, pos);
      }
    } else {
      calc {
        from_bits(bits_n[..pos+1]);
        == (if bits_n[0] then 1 else 0) + 2 * from_bits(bits_n[1..pos+1]);
        == (if bits_n[0] then 1 else 0) + 2 * from_bits(bits_n[1..][..pos]);
        == (if bits_n[0] then 1 else 0) + 2 * (from_bits(bits_n[1..][..pos-1]) + 0);
        == (if bits_n[0] then 1 else 0) + 2 * from_bits(bits_n[1..pos]);
        == from_bits(bits_n[..pos]);
      }
    }
  }
}

lemma ExpInvariantHelper(b: nat, k: nat)
  ensures exp(exp(b, exp(2, k)), 2) == exp(b, exp(2, k+1))
{
  ExpPower(b, exp(2, k), 2);
  ExpAdditive(2, 1, k);
  calc {
    exp(exp(b, exp(2, k)), 2);
    == exp(b, exp(2, k) * 2);
    == exp(b, 2 * exp(2, k));
    == exp(b, exp(2, 1) * exp(2, k));
    == exp(b, exp(2, 1 + k));
    == exp(b, exp(2, k + 1));
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
{
  if n == 0 {
    r := 1;
    return;
  }
  
  var bits_n := bits(n);
  BitsFromBitsIdentity(n);
  assert from_bits(bits_n) == n;
  
  r := 1;
  var base := b;
  var i := 0;
  
  while i < |bits_n|
    invariant 0 <= i <= |bits_n|
    invariant r == exp(b, from_bits(bits_n[..i]))
    invariant base == exp(b, exp(2, i))
    decreases |bits_n| - i
  {
    var old_r := r;
    var old_base := base;
    
    if bits_n[i] {
      r := r * base;
      ExpAdditive(b, from_bits(bits_n[..i]), exp(2, i));
    }
    
    base := base * base;
    ExpInvariantHelper(b, i);
    
    FromBitsBit(bits_n, i);
    
    i := i + 1;
  }
  
  assert bits_n[..|bits_n|] == bits_n;
  assert r == exp(b, from_bits(bits_n));
  assert r == exp(b, n);
}
// </vc-code>
