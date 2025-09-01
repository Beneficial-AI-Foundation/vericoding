function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method Tribonacci(n: nat) returns (result: seq<nat>)
  // post-conditions-start
  ensures |result| == n + 1
  ensures forall i :: 0 <= i <= n ==> result[i] == tri(i)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var res: seq<nat> := [];
  for i := 0 to n
  {
    res := res + [tri(i)];
  }
  result := res;
}
// </vc-code>

