predicate ValidInput(n: int, arr: seq<int>)
{
  n >= 1 && |arr| == n
}

function sum_seq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + sum_seq(s[1..])
}

predicate CorrectResult(n: int, arr: seq<int>, result: int)
  requires ValidInput(n, arr)
{
  (sum_seq(arr) % n == 0 ==> result == n) &&
  (sum_seq(arr) % n != 0 ==> result == n - 1) &&
  (result == n || result == n - 1)
}

// <vc-helpers>
lemma SumSeqComputation(s: seq<int>)
  ensures sum_seq(s) == (if |s| == 0 then 0 else s[0] + sum_seq(s[1..]))
{
  // This lemma makes the definition of sum_seq explicit for verification
}

lemma ModuloProperties(a: int, b: int)
  requires b > 0
  ensures (a % b == 0) || (a % b != 0)
  ensures a % b == 0 <==> exists k :: a == k * b
{
  // Basic modulo properties
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
  requires ValidInput(n, arr)
  ensures CorrectResult(n, arr, result)
// </vc-spec>
// <vc-code>
{
  var total := sum_seq(arr);
  
  if total % n == 0 {
    result := n;
  } else {
    result := n - 1;
  }
  
  assert sum_seq(arr) == total;
  assert (total % n == 0 ==> result == n);
  assert (total % n != 0 ==> result == n - 1);
  assert result == n || result == n - 1;
}
// </vc-code>

