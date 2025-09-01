function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>
lemma TribonacciLemma(n: nat, k: nat, cache: seq<nat>) 
  requires 0 <= k <= n
  requires |cache| == k
  requires forall i :: 0 <= i < k ==> cache[i] == tri(i)
  ensures forall i :: 0 <= i < k ==> cache[i] == tri(i)
  decreases n - k
{
  if k < n {
    var next := tri(k);
    TribonacciLemma(n, k+1, cache + [next]);
  }
}

lemma TribonacciBaseCases() 
  ensures tri(0) == 1
  ensures tri(1) == 3
  ensures tri(2) == 2
{
}
// </vc-helpers>
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
  if n == 0 {
    result := [tri(0)];
    return;
  }
  if n == 1 {
    result := [tri(0), tri(1)];
    return;
  }
  
  result := [tri(0), tri(1)];
  var i := 2;
  while i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == tri(j)
    invariant i <= n + 1
  {
    var next := tri(i);
    result := result + [next];
    i := i + 1;
  }
}
// </vc-code>

