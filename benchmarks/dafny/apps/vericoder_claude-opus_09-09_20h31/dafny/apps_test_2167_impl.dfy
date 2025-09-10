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
lemma sum_seq_bounds(s: seq<int>)
  ensures sum_seq(s) >= 0 || sum_seq(s) < 0
{
  // This is trivially true but helps the verifier
}

lemma sum_seq_append(s: seq<int>, x: int)
  ensures sum_seq(s + [x]) == sum_seq(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert sum_seq([x]) == x + sum_seq([]);
    assert sum_seq([]) == 0;
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    sum_seq_append(s[1..], x);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
  requires ValidInput(n, arr)
  ensures CorrectResult(n, arr, result)
// </vc-spec>
// <vc-code>
{
  var total := 0;
  var i := 0;
  
  // Calculate sum of array
  while i < n
    invariant 0 <= i <= n
    invariant n == |arr|
    invariant total == sum_seq(arr[..i])
  {
    total := total + arr[i];
    assert arr[..i+1] == arr[..i] + [arr[i]];
    sum_seq_append(arr[..i], arr[i]);
    i := i + 1;
  }
  
  assert i == n;
  assert arr[..n] == arr;
  assert total == sum_seq(arr);
  
  // Determine result based on divisibility
  if total % n == 0 {
    result := n;
  } else {
    result := n - 1;
  }
}
// </vc-code>

