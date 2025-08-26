function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}

// <vc-helpers>
// </vc-helpers>

method calcF(n: nat) returns (res: nat)  
 ensures res == F(n)
// </vc-spec>
// <vc-code>
{
  if n <= 2 {
    res := n;
  } else {
    var f_prev3 := 0; // F(0);
    var f_prev2 := 1; // F(1);
    var f_prev1 := 2; // F(2);
    
    var i := 3;
    while i <= n
      invariant 3 <= i <= n + 1
      invariant f_prev3 == F(i-3)
      invariant f_prev2 == F(i-2)
      invariant f_prev1 == F(i-1)
    {
      var f_curr := f_prev1 + f_prev3;
      f_prev3 := f_prev2;
      f_prev2 := f_prev1;
      f_prev1 := f_curr;
      i := i + 1;
    }
    
    res := f_prev1;
  }
}
// </vc-code>