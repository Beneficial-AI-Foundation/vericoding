function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>
lemma TriTermination(n: nat)
  decreases if n % 2 == 0 then 0 else n
  ensures true
{
  if n == 1 {
  } else if n % 2 == 0 {
  } else {
    TriTermination(n - 1);
    TriTermination(n - 2);
    TriTermination(n + 1);
  }
}
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
  for i := 0 to n + 1
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == tri(k)
  {
    res := res + [tri(i)];
    TriTermination(i);
  }
  result := res;
}
// </vc-code>
