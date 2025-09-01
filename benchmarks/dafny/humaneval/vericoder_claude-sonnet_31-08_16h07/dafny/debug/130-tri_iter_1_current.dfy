function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>
lemma TriDecreases(n: nat)
  requires n >= 3 && n % 2 == 1
  ensures n - 1 < n && n - 2 < n
{
}

lemma TriWellDefined(n: nat)
  ensures tri(n) >= 0
{
  if n == 1 {
  } else if n % 2 == 0 {
  } else {
    if n >= 3 {
      TriDecreases(n);
      TriWellDefined(n - 1);
      TriWellDefined(n - 2);
      TriWellDefined(n + 1);
    }
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
  result := [];
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == tri(j)
  {
    var triValue := tri(i);
    result := result + [triValue];
    i := i + 1;
  }
}
// </vc-code>

