//ATOM
function R(n: nat): nat {
  if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

//IMPL
method calcR(n: nat) returns (r: nat)
  ensures r == R(n) 
{
  r := 0;
  var i := 1;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant r == R(i - 1)
  {
    if r > i {
      r := r - i;
    } else {
      r := r + i;
    }
    i := i + 1;
  }
}