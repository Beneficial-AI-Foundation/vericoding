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
    invariant i <= n+1 && |result| == i && forall k :: 0 <= k < i ==> result[k] == tri(k)
  {
    result := result + [tri(i)];
    i := i + 1;
  }
}
// </vc-code>
