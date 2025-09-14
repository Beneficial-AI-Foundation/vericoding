ghost function f2(n: nat): nat {
    if n == 0 then 0
    else 5*f2(n/3) + n%4
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mod2(n:nat) returns (a:nat) 
ensures a == f2(n)
// </vc-spec>
// <vc-code>
{
  var current := n;
  var power := 1;
  var result := 0;
  
  while current != 0
    decreases current
    invariant result + power * f2(current) == f2(n)
  {
    var digit := current % 4;
    result := result + digit * power;
    power := power * 5;
    current := current / 3;
  }
  
  a := result;
}
// </vc-code>

