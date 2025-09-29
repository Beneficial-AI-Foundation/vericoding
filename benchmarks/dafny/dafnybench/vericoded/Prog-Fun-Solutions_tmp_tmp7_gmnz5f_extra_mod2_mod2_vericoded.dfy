ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
// </vc-spec>
// <vc-code>
{
  var m: nat := n;
  a := 0;
  var pow5: nat := 1;
  while m > 0
    decreases m
    invariant a + pow5 * f2(m) == f2(n)
  {
    var mm: nat := m;
    assert mm > 0;
    // compute mm/3 as an int, then as a nat
    var mmdiv_int := mm / 3;
    assert mmdiv_int >= 0;
    var mmdiv: nat := mmdiv_int;
    // compute digit mm % 4 as an int, then as a nat
    var digit_int := mm % 4;
    assert digit_int >= 0;
    var digit: nat := digit_int;
    // unfold definition of f2 for mm>0
    assert f2(mm) == 5 * f2(mmdiv) + digit_int;
    // add contribution to a
    var add_int := pow5 * digit;
    assert add_int >= 0;
    var add: nat := add_int;
    a := a + add;
    // update pow5 := pow5 * 5
    var pow5_int := pow5 * 5;
    assert pow5_int >= 0;
    var pow5n: nat := pow5_int;
    pow5 := pow5n;
    m := mmdiv;
  }
}
// </vc-code>

