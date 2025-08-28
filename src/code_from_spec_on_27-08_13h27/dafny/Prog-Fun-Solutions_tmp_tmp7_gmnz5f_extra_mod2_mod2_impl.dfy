ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

// <vc-helpers>
lemma f2Properties(n: nat)
  ensures f2(n) >= 0
{
  if n == 0 {
    assert f2(0) == 0;
  } else {
    calc {
      f2(n);
      == 5 * f2(n/3) + n%4;
      >= { f2Properties(n/3); }
         5 * 0 + n%4;
      >= 0;
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
// </vc-spec>
// </vc-spec>

// <vc-code>
method Mod2(n: nat) returns (a: nat)
  ensures a == f2(n)
{
  if n == 0 {
    a := 0;
  } else {
    var b := Mod2(n / 3);
    a := 5 * b + n % 4;
  }
}
// </vc-code>
