// <vc-preamble>
function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method calcF(n: nat) returns (res: nat)  
 ensures res == F(n)
// </vc-spec>
// <vc-code>
{
  var a, b, c := 0, 1, 2;
  var i := 0;
  while i < n
    decreases n-i
    invariant 0 <= i <= n
    invariant a == F(i) && b == F(i+1) && c == F(i+2)
   {
    a, b, c := b, c, a + c;        
    i := i + 1;
  }
  res := a;
}
// </vc-code>
