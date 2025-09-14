function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

// <vc-helpers>
// Removed invalid lemma as it attempts to call a method in ensures clause, which is not allowed
// </vc-helpers>

// <vc-spec>
method calcR(n: nat) returns (r: nat)
    ensures r == R(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    r := 0;
  } else {
    var prev := calcR(n-1);
    if prev > n {
      r := prev - n;
    } else {
      r := prev + n;
    }
  }
}
// </vc-code>

