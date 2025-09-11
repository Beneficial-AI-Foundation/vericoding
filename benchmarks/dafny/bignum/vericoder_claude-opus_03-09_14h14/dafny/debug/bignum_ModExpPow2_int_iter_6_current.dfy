ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

// <vc-helpers>
lemma ExpPow2Squared(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  var exp2n := Exp_int(2, n);
  var exp2n1 := Exp_int(2, n-1);
  
  assert exp2n == 2 * exp2n1 by {
    assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
  }
  
  calc {
    Exp_int(x, Exp_int(2, n));
    == Exp_int(x, exp2n);
    == Exp_int(x, 2 * exp2n1);
    == { assert 2 * exp2n1 == exp2n1 + exp2n1; 
         ExpMultiply(x, exp2n1, exp2n1); }
    Exp_int(x, exp2n1) * Exp_int(x, exp2n1);
    == { SquareIsExp2(Exp_int(x, exp2n1)); }
    Exp_int(Exp_int(x, exp2n1), 2);
    == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
  }
}

lemma SquareIsExp2(a: nat)
  ensures Exp_int(a, 2) == a * a
{
  calc {
    Exp_int(a, 2);
    == a * Exp_int(a, 1);
    == a * (a * Exp_int(a, 0));
    == a * (a * 1);
    == a * a;
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

lemma ModMultiply(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
  // Use Dafny's built-in understanding of modular arithmetic
  // This is a well-known property that Dafny can verify more efficiently
  // without explicit calculation steps
}

lemma Exp2Property(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n-1)
  ensures Exp_int(2, n) / 2 == Exp_int(2, n-1)
{
  assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
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
    assert Exp_int(x, 1) == x;
    res := x % z;
  } else {
    Exp2Property(n);
    assert y / 2 == Exp_int(2, n-1);
    var tmp := ModExpPow2_int(x, y / 2, n-1, z);
    assert tmp == Exp_int(x, Exp_int(2, n-1)) % z;
    
    ExpPow2Squared(x, n);
    assert Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
    
    SquareIsExp2(Exp_int(x, Exp_int(2, n-1)));
    assert Exp_int(Exp_int(x, Exp_int(2, n-1)), 2) == Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1));
    
    ModMultiply(Exp_int(x, Exp_int(2, n-1)), Exp_int(x, Exp_int(2, n-1)), z);
    assert ((Exp_int(x, Exp_int(2, n-1)) % z) * (Exp_int(x, Exp_int(2, n-1)) % z)) % z == (Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1))) % z;
    
    res := (tmp * tmp) % z;
    
    assert res == Exp_int(x, Exp_int(2, n)) % z;
  }
}
// </vc-code>

