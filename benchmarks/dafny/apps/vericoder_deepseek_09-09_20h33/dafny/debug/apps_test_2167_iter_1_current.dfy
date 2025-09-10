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
  
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant total == sum_seq(arr[0..i])
  {
    total := total + arr[i];
    i := i + 1;
  }
  
  if total % n == 0 {
    result := n;
  } else {
    result := n - 1;
  }
}
// </vc-code>

