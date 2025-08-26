method gaussian (size:int, q: array<real>, q_hat: array<real>) returns (out: array<real>)
requires q_hat.Length==size
requires q.Length==size
requires size > 0
requires arraySquaredSum(q_hat[..]) <= 1.0
// </vc-spec>
// <vc-code>
{
  out := new real[size];
  var i := 0;
  while i < size
    invariant 0 <= i <= size
  {
    out[i] := q[i] + q_hat[i];
    i := i + 1;
  }
}
// </vc-code>

function arraySquaredSum(a: seq<real>): real
requires |a| > 0
{
  if |a| == 1 then 
    a[0]*a[0]
  else 
    (a[0]*a[0]) + arraySquaredSum(a[1..])
}