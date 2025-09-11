ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpAddition(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a);
    assert Exp_int(x, 0) == 1;
  } else {
    ExpAddition(x, a, b - 1);
    assert Exp_int(x, a + b) == Exp_int(x, a + (b - 1) + 1);
    assert Exp_int(x, (b - 1) + 1) == x * Exp_int(x, b - 1);
  }
}

lemma ModMultiplication(a: nat, b: nat, z: nat)
  requires z > 0
  ensures (a * b) % z == ((a % z) * (b % z)) % z
{
  // Using the fact that a = (a/z)*z + (a%z) and b = (b/z)*z + (b%z)
  var qa := a / z;
  var ra := a % z;
  var qb := b / z;
  var rb := b % z;
  
  assert a == qa * z + ra;
  assert b == qb * z + rb;
  
  calc {
    a * b;
    == (qa * z + ra) * (qb * z + rb);
    == qa * z * qb * z + qa * z * rb + ra * qb * z + ra * rb;
    == z * (qa * qb * z + qa * rb + ra * qb) + ra * rb;
  }
  
  assert (a * b) % z == (ra * rb) % z;
  assert ra == a % z;
  assert rb == b % z;
}

function ComputePow2(n: nat): nat
{
  if n == 0 then 1 else 2 * ComputePow2(n - 1)
}

lemma ComputePow2Correct(n: nat)
  ensures ComputePow2(n) == Exp_int(2, n)
{
  if n == 0 {
    assert ComputePow2(0) == 1 == Exp_int(2, 0);
  } else {
    ComputePow2Correct(n - 1);
    assert ComputePow2(n) == 2 * ComputePow2(n - 1) == 2 * Exp_int(2, n - 1) == Exp_int(2, n);
  }
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
    if y == 0 {
      res := 1;
    } else {
      res := x % z;
    }
  } else {
    var powerOfTwo := ComputePow2(n);
    ComputePow2Correct(n);
    assert powerOfTwo == Exp_int(2, n);
    
    if y < powerOfTwo {
      res := ModExp_int(x, y, n - 1, z);
    } else {
      var highPart := ModExpPow2_int(x, powerOfTwo, n, z);
      var lowPart := ModExp_int(x, y - powerOfTwo, n - 1, z);
      res := (highPart * lowPart) % z;
      
      assert powerOfTwo == Exp_int(2, n);
      ExpAddition(x, powerOfTwo, y - powerOfTwo);
      assert Exp_int(x, y) == Exp_int(x, powerOfTwo) * Exp_int(x, y - powerOfTwo);
      assert highPart == Exp_int(x, powerOfTwo) % z;
      assert lowPart == Exp_int(x, y - powerOfTwo) % z;
      ModMultiplication(Exp_int(x, powerOfTwo), Exp_int(x, y - powerOfTwo), z);
      assert Exp_int(x, y) % z == ((Exp_int(x, powerOfTwo) % z) * (Exp_int(x, y - powerOfTwo) % z)) % z;
      assert res == Exp_int(x, y) % z;
    }
  }
}
// </vc-code>

