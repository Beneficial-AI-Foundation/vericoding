ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

// <vc-helpers>
lemma f2_calculation(n: nat)
  ensures n == 0 ==> f2(n) == 0
  ensures n > 0 ==> f2(n) == 5 * f2(n / 3) + n % 4
{
  if n == 0 {
    assert f2(n) == 0;
  } else {
    assert f2(n) == 5 * f2(n / 3) + n % 4;
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
{
  if n == 0 {
    a := 0;
  } else {
    var sub := mod2(n / 3);
    a := 5 * sub + n % 4;
  }
}
// </vc-code>
