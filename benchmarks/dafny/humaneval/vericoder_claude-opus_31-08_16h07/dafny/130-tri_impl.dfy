function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>
lemma TriOddExpansion(n: nat)
  requires n > 1 && n % 2 == 1
  ensures tri(n) == tri(n - 1) + tri(n - 2) + (1 + (n + 1) / 2)
{
  assert tri(n + 1) == 1 + (n + 1) / 2;
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
  result := [];
  var i := 0;
  
  while i <= n
    invariant 0 <= i <= n + 1
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == tri(j)
  {
    if i == 0 {
      result := result + [1];
    } else if i == 1 {
      result := result + [3];
    } else if i % 2 == 0 {
      result := result + [1 + i / 2];
    } else {
      // i is odd and i > 1
      var triNext := 1 + (i + 1) / 2;
      TriOddExpansion(i);
      result := result + [result[i - 1] + result[i - 2] + triNext];
    }
    i := i + 1;
  }
}
// </vc-code>

