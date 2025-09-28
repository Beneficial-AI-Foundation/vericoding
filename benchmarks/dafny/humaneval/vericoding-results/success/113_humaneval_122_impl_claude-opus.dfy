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

// </vc-helpers>

// <vc-spec>
method add_elements(arr: seq<int>, k: int) returns (result: int)
  requires ValidInput(arr, k)
  ensures result == sum_valid_elements(arr, k)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant result == sum_valid_elements_up_to(arr, i)
  {
    var current := if -99 <= arr[i] <= 99 then arr[i] else 0;
    result := result + current;
    i := i + 1;
  }
}
// </vc-code>
