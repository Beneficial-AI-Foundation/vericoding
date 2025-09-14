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
    // Base case: bits(0) = [], from_bits([]) = 0
  } else {
    // Inductive case
    var bit_seq := bits(n);
    assert bit_seq == [if (n % 2 == 0) then false else true] + bits(n/2);
    
    calc {
      from_bits(bits(n));
      from_bits([if (n % 2 == 0) then false else true] + bits(n/2));
      (if (if (n % 2 == 0) then false else true) then 1 else 0) + 2 * from_bits(bits(n/2));
      (if (n % 2 == 1) then 1 else 0) + 2 * from_bits(bits(n/2));
      { BitsFromBitsIdentity(n/2); }
      (if (n % 2 == 1) then 1 else 0) + 2 * (n/2);
      (n % 2) + 2 * (n/2);
      { assert n == 2 * (n/2) + (n % 2); }
      n;
    }
  }
}

lemma ExpBasicProperty(b: nat)
  ensures exp(b, 2) == b * b
{
  calc {
    exp(b, 2);
    b * exp(b, 1);
    b * (b * exp(b, 0));
    b * (b * 1);
    b * b;
  }
}

lemma ExpMultiplication(b: nat, m: nat, n: nat)
  ensures exp(b, m + n) == exp(b, m) * exp(b, n)
  decreases m
{
  if m == 0 {
    calc {
      exp(b, 0 + n);
      exp(b, n);
      1 * exp(b, n);
      exp(b, 0) * exp(b, n);
    }
  } else {
    calc {
      exp(b, m + n);
      b * exp(b, m + n - 1);
      b * exp(b, (m - 1) + n);
      { ExpMultiplication(b, m - 1, n); }
      b * (exp(b, m - 1) * exp(b, n));
      (b * exp(b, m - 1)) * exp(b, n);
      exp(b, m) * exp(b, n);
    }
  }
}

lemma ExpPowerRule(b: nat, m: nat, n: nat)
  ensures exp(b, m * n) == exp(exp(b, m), n)
  decreases n
{
  if n == 0 {
    calc {
      exp(b, m * 0);
      exp(b, 0);
      1;
      exp(exp(b, m), 0);
    }
  } else if n == 1 {
    calc {
      exp(b, m * 1);
      exp(b, m);
      exp(exp(b, m), 1);
    }
  } else {
    calc {
      exp(b, m * n);
      { assert m * n == m + m * (n - 1); }
      exp(b, m + m * (n - 1));
      { ExpMultiplication(b, m, m * (n - 1)); }
      exp(b, m) * exp(b, m * (n - 1));
      { ExpPowerRule(b, m, n - 1); }
      exp(b, m) * exp(exp(b, m), n - 1);
      exp(exp(b, m), n);
    }
  }
}

lemma ExpBySquaring(b: nat, n: nat)
  ensures exp(b, n) == if n == 0 then 1 
                       else if n % 2 == 0 then exp(b * b, n / 2)
                       else b * exp(b * b, n / 2)
  decreases n
{
  if n == 0 {
    // Base case
  } else if n % 2 == 0 {
    // Even case
    calc {
      exp(b, n);
      { assert n == 2 * (n/2); }
      exp(b, 2 * (n/2));
      { ExpPowerRule(b, 2, n/2); }
      exp(exp(b, 2), n/2);
      { ExpBasicProperty(b); }
      exp(b * b, n/2);
    }
  } else {
    // Odd case
    calc {
      exp(b, n);
      { assert n == 2 * (n/2) + 1; }
      exp(b, 2 * (n/2) + 1);
      { ExpMultiplication(b, 2 * (n/2), 1); }
      exp(b, 2 * (n/2)) * exp(b, 1);
      exp(b, 2 * (n/2)) * b;
      { ExpPowerRule(b, 2, n/2); }
      exp(exp(b, 2), n/2) * b;
      { ExpBasicProperty(b); }
      exp(b * b, n/2) * b;
      b * exp(b * b, n/2);
    }
  }
}

lemma FastExpInvariantHelper(r: nat, base: nat, exponent: nat, b: nat, n: nat)
  requires r * exp(base, exponent) == exp(b, n)
  requires exponent > 0
  ensures if exponent % 2 == 1 
          then (r * base) * exp(base * base, exponent / 2) == exp(b, n)
          else r * exp(base * base, exponent / 2) == exp(b, n)
{
  if exponent % 2 == 1 {
    calc {
      (r * base) * exp(base * base, exponent / 2);
      r * (base * exp(base * base, exponent / 2));
      { ExpBySquaring(base, exponent); }
      r * exp(base, exponent);
      exp(b, n);
    }
  } else {
    calc {
      r * exp(base * base, exponent / 2);
      { ExpBySquaring(base, exponent); }
      r * exp(base, exponent);
      exp(b, n);
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
  var base := b;
  var exponent := n;
  
  while exponent > 0
    invariant r * exp(base, exponent) == exp(b, n)
    decreases exponent
  {
    if exponent % 2 == 1 {
      FastExpInvariantHelper(r, base, exponent, b, n);
      r := r * base;
    } else {
      FastExpInvariantHelper(r, base, exponent, b, n);
    }
    base := base * base;
    exponent := exponent / 2;
  }
}
// </vc-code>

