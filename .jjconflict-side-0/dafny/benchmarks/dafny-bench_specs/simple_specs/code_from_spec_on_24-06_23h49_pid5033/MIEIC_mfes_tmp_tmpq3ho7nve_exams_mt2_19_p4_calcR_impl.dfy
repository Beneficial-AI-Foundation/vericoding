//ATOM
function R(n: nat): nat {
  if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

//IMPL calcR
method calcR(n: nat) returns (r: nat)
  ensures r == R(n) 
{
  /* code modified by LLM (iteration 1): implemented iterative computation with loop invariant */
  if n == 0 {
    r := 0;
  } else {
    var i := 0;
    r := 0;
    while i < n
      invariant 0 <= i <= n
      invariant r == R(i)
    {
      i := i + 1;
      if r > i {
        r := r - i;
      } else {
        r := r + i;
      }
    }
  }
}