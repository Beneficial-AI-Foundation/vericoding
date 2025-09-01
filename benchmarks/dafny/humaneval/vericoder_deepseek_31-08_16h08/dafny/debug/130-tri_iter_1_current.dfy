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
  requires |cache| == n+1
  requires forall i :: 0 <= i < k ==> cache[i] == tri(i)
  ensures forall i :: 0 <= i < k ==> cache[i] == tri(i)
  decreases n - k
{
  if k < n {
    var next := if k == 0 then 3
               else if k == 1 then if n > 0 then 1 + 1/2 else 1
               else if k == 2 then tri(0) + tri(1) + tri(3)
               else cache[k-1] + cache[k-2] + tri(k+1);
    TribonacciLemma(n, k+1, cache + [next]);
  }
}

lemma TribonacciBaseCases() 
  ensures tri(0) == 1 + 0/2
  ensures tri(1) == 3
  ensures tri(2) == 1 + 2/2
{
  // Base cases verified by function definition
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
    invariant |result| == i + 1
    invariant forall j :: 0 <= j < i ==> result[j] == tri(j)
    invariant 2 <= i <= n + 1
  {
    if i == 2 {
      result := result + [1 + i/2];
    } else {
      result := result + [result[i-1] + result[i-2] + tri(i+1)];
    }
    i := i + 1;
  }
}
// </vc-code>

