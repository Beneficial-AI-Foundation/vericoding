ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

// <vc-helpers>
lemma f2_lemma(n: nat)
  ensures f2(n) == if n == 0 then 0 else 5*f2(n/3) + n%4
{
}

lemma f2_zero()
  ensures f2(0) == 0
{
}

lemma f2_rec(n: nat)
  requires n > 0
  ensures f2(n) == 5*f2(n/3) + n%4
{
}
// </vc-helpers>

// <vc-spec>
method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    a := 0;
  } else {
    var k := n/3;
    var r := n%4;
    var inner := mod2(k);
    a := 5*inner + r;
  }
}
// </vc-code>

