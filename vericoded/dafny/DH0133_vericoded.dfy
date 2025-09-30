// <vc-preamble>
function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Tribonacci(n: nat) returns (result: seq<nat>)

  ensures |result| == n + 1
  ensures forall i :: 0 <= i <= n ==> result[i] == tri(i)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == tri(j)
  {
    result := result + [tri(i)];
    i := i + 1;
  }
}
// </vc-code>
