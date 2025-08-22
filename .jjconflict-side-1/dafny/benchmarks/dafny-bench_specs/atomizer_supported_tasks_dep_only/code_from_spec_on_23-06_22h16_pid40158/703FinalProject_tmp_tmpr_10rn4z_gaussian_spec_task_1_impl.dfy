// VERIFY USING DAFNY:
// /Applications/dafny/dafny /Users/apple/GaussianDP/Dafny/gaussian.dfy
//IMPL gaussian
method gaussian (size:int, q: array<real>, q_hat: array<real>) returns (out: array<real>)
requires q_hat.Length==size
requires q.Length==size
requires size > 0
requires arraySquaredSum(q_hat[..]) <= 1.0
{
    out := new real[size];
    var i := 0;
    while i < size
        invariant 0 <= i <= size
    {
        out[i] := 0.0;
        i := i + 1;
    }
}

// ATOM 
function arraySquaredSum(a: seq<real>): real
requires |a| > 0
{
  if |a| == 1 then 
    a[0]*a[0]
  else 
    (a[0]*a[0]) + arraySquaredSum(a[1..])
}