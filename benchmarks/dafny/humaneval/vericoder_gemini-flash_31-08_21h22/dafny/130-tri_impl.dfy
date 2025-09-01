function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>
function trib(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else trib(n - 1) + trib(n - 2) + trib(n + 1)
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
  var result_seq: seq<nat> := [];
  if n == 0 {
    result_seq := [tri(0)];
  } else if n == 1 {
    result_seq := [tri(0), tri(1)];
  } else {
    result_seq := [tri(0), tri(1)];
    var i := 2;
    while i <= n
      invariant 0 <= i <= n + 1
      invariant |result_seq| == i
      invariant forall k :: 0 <= k < i ==> result_seq[k] == tri(k)
    {
      if i % 2 == 0 {
        result_seq := result_seq + [1 + i / 2];
      } else {
        result_seq := result_seq + [result_seq[i - 1] + result_seq[i - 2] + trib(i + 1)]; // Use trib for the recursion to avoid recomputing based on tri
      }
      i := i + 1;
    }
  }
  return result_seq;
}
// </vc-code>

