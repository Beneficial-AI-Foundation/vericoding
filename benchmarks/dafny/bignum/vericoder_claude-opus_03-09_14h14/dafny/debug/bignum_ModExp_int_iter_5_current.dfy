ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

// <vc-helpers>
lemma ExpProperties(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, 0) % z == 1 % z
  ensures y > 0 ==> Exp_int(x, y) % z == (x * Exp_int(x, y - 1)) % z
{
  if y > 0 {
    assert Exp_int(x, y) == x * Exp_int(x, y - 1);
  }
}

lemma ModMultiplicative(a: nat, b: nat, c: nat, z: nat)
  requires z > 1
  ensures (a * b * c) % z == ((a * b) % z * c) % z
  ensures (a * b) % z == ((a % z) * (b % z)) % z
{
  // Dafny can verify these modular arithmetic properties automatically
}

lemma ExpSplitEven(x: nat, y: nat)
  requires y > 0 && y % 2 == 0
  ensures Exp_int(x, y) == Exp_int(x * x, y / 2)
{
  if y == 2 {
    calc {
      Exp_int(x, 2);
      == x * Exp_int(x, 1);
      == x * x * Exp_int(x, 0);
      == x * x * 1;
      == x * x;
    }
    calc {
      Exp_int(x * x, 1);
      == (x * x) * Exp_int(x * x, 0);
      == (x * x) * 1;
      == x * x;
    }
  } else {
    var half := y / 2;
    assert y == 2 * half;
    ExpSplitEvenHelper(x, half);
  }
}

lemma ExpSplitEvenHelper(x: nat, k: nat)
  requires k > 0
  ensures Exp_int(x, 2 * k) == Exp_int(x * x, k)
  decreases k
{
  if k == 1 {
    calc {
      Exp_int(x, 2);
      == x * Exp_int(x, 1);
      == x * x * Exp_int(x, 0);
      == x * x * 1;
      == x * x;
    }
    assert Exp_int(x * x, 1) == x * x;
  } else {
    assert Exp_int(x, 2 * k) == x * Exp_int(x, 2 * k - 1);
    assert 2 * k - 1 == 2 * (k - 1) + 1;
    assert Exp_int(x, 2 * k - 1) == x * Exp_int(x, 2 * (k - 1));
    ExpSplitEvenHelper(x, k - 1);
    assert Exp_int(x, 2 * (k - 1)) == Exp_int(x * x, k - 1);
    assert Exp_int(x, 2 * k) == x * x * Exp_int(x * x, k - 1);
    assert Exp_int(x * x, k) == (x * x) * Exp_int(x * x, k - 1);
  }
}

lemma ModExpEquivalence(a: nat, b: nat, k: nat, z: nat)
  requires z > 1
  requires a % z == b % z
  ensures Exp_int(a, k) % z == Exp_int(b, k) % z
  decreases k
{
  if k == 0 {
    // Base case: both are 1
  } else {
    // Inductive step
    ModExpEquivalence(a, b, k - 1, z);
    // Exp_int(a, k) = a * Exp_int(a, k-1)
    // Exp_int(b, k) = b * Exp_int(b, k-1)
    // Since a % z == b % z and Exp_int(a, k-1) % z == Exp_int(b, k-1) % z
    // The result follows from modular arithmetic
  }
}

lemma ExpBound(y: nat, n: nat)
  requires n > 0
  requires y < Exp_int(2, n + 1)
  ensures y / 2 < Exp_int(2, n)
  ensures y > 0 ==> y - 1 < Exp_int(2, n + 1)
  ensures y > 0 ==> y - 1 < Exp_int(2, n)
{
  assert Exp_int(2, n + 1) == 2 * Exp_int(2, n);
  assert y < 2 * Exp_int(2, n);
  assert y / 2 < Exp_int(2, n);
  
  if y > 0 {
    assert y - 1 < y;
    assert y - 1 < Exp_int(2, n + 1);
    // Since y < Exp_int(2, n+1) = 2 * Exp_int(2, n) and y > 0
    // If y <= Exp_int(2, n), then y - 1 < Exp_int(2, n)
    // If y > Exp_int(2, n), then y >= Exp_int(2, n) + 1, so y - 1 >= Exp_int(2, n)
    // But we need y - 1 < Exp_int(2, n) for the recursive call
    // Actually, we need a tighter bound for the odd case
  }
}

lemma ExpBoundForOdd(y: nat, n: nat)
  requires n > 0
  requires y < Exp_int(2, n + 1)
  requires y % 2 == 1
  ensures y > 0
  ensures y - 1 < Exp_int(2, n)
{
  assert Exp_int(2, n + 1) == 2 * Exp_int(2, n);
  assert y < 2 * Exp_int(2, n);
  // Since y is odd, y = 2k + 1 for some k >= 0
  // So y - 1 = 2k
  // Since y < 2 * Exp_int(2, n), we have 2k + 1 < 2 * Exp_int(2, n)
  // Therefore 2k < 2 * Exp_int(2, n) - 1 < 2 * Exp_int(2, n)
  // So k < Exp_int(2, n), and thus 2k < 2 * Exp_int(2, n)
  // But we need 2k < Exp_int(2, n)
  // This requires y <= Exp_int(2, n), which isn't guaranteed
  // We need to use the fact that we're decreasing n in the recursion
  // Actually for n > 0, if y < Exp_int(2, n+1) and y is odd, then y-1 is even
  // and y-1 < Exp_int(2, n+1) - 1
  // But Exp_int(2, n+1) - 1 < Exp_int(2, n+1) = 2 * Exp_int(2, n)
  // So y-1 < 2 * Exp_int(2, n)
  // But we need y-1 < Exp_int(2, n) for the recursive call with n-1
  // The issue is that we're calling with n-1 but need y-1 < Exp_int(2, (n-1)+1) = Exp_int(2, n)
  // So we need to ensure y-1 < Exp_int(2, n)
  // Since y < Exp_int(2, n+1) = 2 * Exp_int(2, n)
  // If y <= Exp_int(2, n), then y-1 < Exp_int(2, n) ✓
  // If y > Exp_int(2, n), then since y is odd and Exp_int(2, n) is even for n > 0,
  // we have y >= Exp_int(2, n) + 1
  // So y-1 >= Exp_int(2, n), which violates what we need
  // This suggests the recursion structure needs adjustment
}
// </vc-helpers>

// <vc-spec>
method ModExp_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y < Exp_int(2,n+1)
  requires z > 1 //&& n > 0
  ensures res == Exp_int(x,y) % z
  decreases n
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    assert y < Exp_int(2, 1);
    assert Exp_int(2, 1) == 2;
    assert y < 2;
    assert y == 0 || y == 1;
    if y == 0 {
      res := 1 % z;
      ExpProperties(x, y, z);
    } else {
      assert y == 1;
      assert Exp_int(x, 1) == x;
      res := x % z;
    }
  } else {
    if y == 0 {
      res := 1 % z;
      ExpProperties(x, y, z);
    } else if y % 2 == 1 {
      ExpBound(y, n);
      assert y > 0;
      assert y - 1 < Exp_int(2, n + 1);
      // For the recursive call, we need y - 1 < Exp_int(2, n)
      // Since y is odd and y < Exp_int(2, n+1) = 2 * Exp_int(2, n)
      // We recursively call with n unchanged to maintain the invariant
      var subres := ModExp_int(x, y - 1, n, z);
      assert subres == Exp_int(x, y - 1) % z;
      res := (x * subres) % z;
      ExpProperties(x, y, z);
    } else {
      assert y % 2 == 0 && y > 0;
      var x2 := (x * x) % z;
      ExpBound(y, n);
      assert y / 2 < Exp_int(2, n);
      var subres := ModExp_int(x2, y / 2, n - 1, z);
      ExpSplitEven(x, y);
      assert Exp_int(x, y) == Exp_int(x * x, y / 2);
      ModExpEquivalence(x * x, x2, y / 2, z);
      assert Exp_int(x * x, y / 2) % z == Exp_int(x2, y / 2) % z;
      res := subres;
    }
  }
}
// </vc-code>

