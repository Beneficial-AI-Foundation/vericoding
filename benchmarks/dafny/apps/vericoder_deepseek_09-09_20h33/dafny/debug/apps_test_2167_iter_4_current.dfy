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
lemma sum_mod_property(n: int, s: seq<int>)
  requires n > 0
  ensures (sum_seq(s) % n == 0) || (sum_seq(s) % n != 0)
{
  // Trivial lemma: any integer modulo n is either 0 or not 0
}

lemma sum_mod_result(n: int, s: seq<int>)
  requires n > 0
  ensures (sum_seq(s) % n == 0 ==> sum_seq(s) % n == 0) && 
          (sum_seq(s) % n != 0 ==> sum_seq(s) % n != 0)
{
  // Another trivial lemma to help with the proof
}

lemma sum_seq_slice_property(arr: seq<int>, i: int)
  requires 0 <= i <= |arr|
  ensures sum_seq(arr[0..i]) == if i == 0 then 0 else sum_seq(arr[0..i-1]) + arr[i-1]
{
  if i == 0 {
    // Base case
  } else {
    // Recursive definition of sum_seq
    var prefix := arr[0..i-1];
    calc {
      sum_seq(arr[0..i]);
      sum_seq(prefix + [arr[i-1]]);
      sum_seq(prefix) + sum_seq([arr[i-1]]);
      sum_seq(prefix) + arr[i-1];
    }
  }
}

ghost function full_sum(n: int, arr: seq<int>): int
  requires ValidInput(n, arr)
  ensures full_sum(n, arr) == sum_seq(arr)
{
  sum_seq(arr)
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
  
  ghost var arr_sum := sum_seq(arr);
  
  while i <= |arr|
    invariant 0 <= i <= |arr|
    invariant total == sum_seq(arr[0..i])
  {
    if i < |arr| {
      total := total + arr[i];
      i := i + 1;
      
      // Help the verifier with lemma about sum_seq property
      sum_seq_slice_property(arr, i);
    } else {
      i := i + 1;  // Exit condition
    }
  }
  
  assert total == arr_sum;
  
  var res: int;
  if total % n == 0 {
    res := n;
  } else {
    res := n - 1;
  }
  
  sum_mod_property(n, arr);
  result := res;
}
// </vc-code>

