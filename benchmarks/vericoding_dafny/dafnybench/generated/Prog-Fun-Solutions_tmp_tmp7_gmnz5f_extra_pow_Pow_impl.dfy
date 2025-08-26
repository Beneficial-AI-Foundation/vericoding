ghost function pow(a: int, e: nat): int {
    if e == 0 then 1 else a*pow(a, e-1)
}

// <vc-helpers>
lemma PowPositive(a: nat, n: nat)
ensures pow(a, n) >= 0
{
    if n == 0 {
        // pow(a, 0) == 1 >= 0
    } else {
        PowPositive(a, n-1);
        // pow(a, n) == a * pow(a, n-1) >= 0 since a >= 0 and pow(a, n-1) >= 0
    }
}

lemma PowAdditive(a: int, m: nat, n: nat)
ensures pow(a, m + n) == pow(a, m) * pow(a, n)
{
    if m == 0 {
        // pow(a, 0 + n) == pow(a, n) == 1 * pow(a, n) == pow(a, 0) * pow(a, n)
    } else {
        PowAdditive(a, m-1, n);
        // pow(a, m + n) == a * pow(a, (m-1) + n) == a * pow(a, m-1) * pow(a, n) == pow(a, m) * pow(a, n)
    }
}
// </vc-helpers>

// <vc-spec>
method Pow(a: nat, n: nat) returns (y: nat)
ensures y == pow(a, n)
// </vc-spec>
// <vc-code>
{
  y := 1;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant y == pow(a, i)
    invariant y >= 0
  {
    y := y * a;
    i := i + 1;
    
    // Prove that the invariant holds after the update
    PowAdditive(a, i-1, 1);
  }
  
  PowPositive(a, n);
}
// </vc-code>