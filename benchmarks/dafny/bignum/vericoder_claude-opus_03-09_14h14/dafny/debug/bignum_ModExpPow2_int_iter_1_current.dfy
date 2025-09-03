ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

// <vc-helpers>
lemma ExpPow2Squared(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  calc {
    Exp_int(x, Exp_int(2, n));
    == Exp_int(x, 2 * Exp_int(2, n-1));
    == { ExpMultiply(x, Exp_int(2, n-1), Exp_int(2, n-1)); }
    Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1));
    == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
  }
}

lemma ExpMultiply(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if a == 0 {
    assert Exp_int(x, a + b) == Exp_int(x, b);
    assert Exp_int(x, a) * Exp_int(x, b) == 1 * Exp_int(x, b) == Exp_int(x, b);
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, a + b - 1);
      == { assert a + b - 1 == (a - 1) + b; }
      x * Exp_int(x, (a - 1) + b);
      == { ExpMultiply(x, a - 1, b); }
      x * (Exp_int(x, a - 1) * Exp_int(x, b));
      == (x * Exp_int(x, a - 1)) * Exp_int(x, b);
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    assert y == 1;
    res := x % z;
    assert res == Exp_int(x, 1) % z;
  } else {
    var tmp := ModExpPow2_int(x, Exp_int(2, n-1), n-1, z);
    assert tmp == Exp_int(x, Exp_int(2, n-1)) % z;
    
    var squared := (tmp * tmp) % z;
    ExpPow2Squared(x, n);
    assert Exp_int(x, y) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
    assert Exp_int(Exp_int(x, Exp_int(2, n-1)), 2) == Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1));
    
    calc {
      squared;
      == (tmp * tmp) % z;
      == ((Exp_int(x, Exp_int(2, n-1)) % z) * (Exp_int(x, Exp_int(2, n-1)) % z)) % z;
      == { ModMultiply(Exp_int(x, Exp_int(2, n-1)), Exp_int(x, Exp_int(2, n-1)), z); }
      (Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1))) % z;
      == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2) % z;
      == Exp_int(x, y) % z;
    }
    
    res := squared;
  }
}

lemma ModMultiply(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
}
// </vc-code>

