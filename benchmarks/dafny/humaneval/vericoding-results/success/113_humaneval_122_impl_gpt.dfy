// <vc-preamble>

predicate ValidInput(arr: seq<int>, k: int) {
  1 <= |arr| <= 100 && 1 <= k <= |arr|
}

function sum_valid_elements(arr: seq<int>, k: int): int
  requires 0 <= k <= |arr|
{
  sum_valid_elements_up_to(arr, k)
}

function sum_valid_elements_up_to(arr: seq<int>, n: int): int
  requires 0 <= n <= |arr|
{
  if n == 0 then 0
  else 
    var current := if -99 <= arr[n-1] <= 99 then arr[n-1] else 0;
    sum_valid_elements_up_to(arr, n-1) + current
}
// </vc-preamble>

// <vc-helpers>
lemma StepSumLemma(arr: seq<int>, i: nat)
  requires i < |arr|
  ensures sum_valid_elements_up_to(arr, i+1) == sum_valid_elements_up_to(arr, i) + (if -99 <= arr[i] <= 99 then arr[i] else 0)
{
}

// </vc-helpers>

// <vc-spec>
method add_elements(arr: seq<int>, k: int) returns (result: int)
  requires ValidInput(arr, k)
  ensures result == sum_valid_elements(arr, k)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var acc := 0;
  while i < k
    invariant 0 <= i <= k
    invariant k <= |arr|
    invariant acc == sum_valid_elements_up_to(arr, i)
    decreases k - i
  {
    assert i < |arr|;
    var current := if -99 <= arr[i] <= 99 then arr[i] else 0;
    acc := acc + current;
    i := i + 1;
  }
  assert sum_valid_elements(arr, k) == sum_valid_elements_up_to(arr, k);
  result := acc;
}
// </vc-code>
