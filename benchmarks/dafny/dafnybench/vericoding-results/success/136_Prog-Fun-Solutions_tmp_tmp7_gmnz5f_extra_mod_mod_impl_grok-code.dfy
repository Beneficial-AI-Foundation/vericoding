ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mod(n:nat) returns (a:nat) 
ensures a == f(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 1;
  } else if n % 2 == 0 {
    var rec := mod(n / 2);
    return 1 + 2 * rec;
  } else {
    var rec := mod(n / 2);
    return 2 * rec;
  }
}
// </vc-code>

