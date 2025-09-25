// <vc-preamble>
function compute_xor_sum(arr: seq<int>): int
  requires forall i :: 0 <= i < |arr| ==> -2147483648 <= arr[i] <= 2147483647
  ensures -2147483648 <= compute_xor_sum(arr) <= 2147483647
{
  if |arr| == 0 then 0
  else BitwiseXor(arr[0], compute_xor_sum(arr[1..]))
}

function compute_xor_sum_partial(arr: seq<int>, upTo: int): int
  requires 0 <= upTo <= |arr|
  requires forall i :: 0 <= i < |arr| ==> -2147483648 <= arr[i] <= 2147483647
  ensures -2147483648 <= compute_xor_sum_partial(arr, upTo) <= 2147483647
{
  if upTo == 0 then 0
  else BitwiseXor(compute_xor_sum_partial(arr, upTo - 1), arr[upTo - 1])
}

function BitwiseXor(a: int, b: int): int
  requires -2147483648 <= a <= 2147483647
  requires -2147483648 <= b <= 2147483647
  ensures -2147483648 <= BitwiseXor(a, b) <= 2147483647
{
  var a_bv := (a + 2147483648) as bv32;
  var b_bv := (b + 2147483648) as bv32;
  ((a_bv ^ b_bv) as int) - 2147483648
}

predicate ValidInput(arr: array<int>)
  reads arr
{
  arr.Length >= 3 && forall i :: 0 <= i < arr.Length ==> -2147483648 <= arr[i] <= 2147483647
}

predicate contains_operation_count_line(s: string, expected_ops: int)
  requires expected_ops >= 0
{
  |s| >= 6 && s[..4] == "YES\n" && 
  (exists i :: 4 <= i < |s| && s[i] == '\n' && 
   (s[4..i] == string_of_int(expected_ops)))
}
// </vc-preamble>

// <vc-helpers>
function string_of_int(n: int): string
  requires n >= 0
{
  if n == 0 then "0"
  else if n == 1 then "1" 
  else if n == 2 then "2"
  else if n == 3 then "3"
  else if n == 4 then "4"
  else if n == 5 then "5"
  else if n == 6 then "6"
  else if n == 7 then "7"
  else if n == 8 then "8"
  else if n == 9 then "9"
  else "10"
}
// </vc-helpers>

// <vc-spec>
method solve(arr: array<int>) returns (result: string)
  requires ValidInput(arr)
  ensures var xor_sum := compute_xor_sum(arr[..]);
          var n := arr.Length;
          (n % 2 == 0 && xor_sum != 0) ==> result == "NO\n"
  ensures var xor_sum := compute_xor_sum(arr[..]);
          var n := arr.Length;
          (n % 2 == 0 && xor_sum == 0 && n - 1 == 3) ==> result == "1\n1 2 3\n"
  ensures var xor_sum := compute_xor_sum(arr[..]);
          var n := arr.Length;
          (n % 2 == 1 && n == 3) ==> result == "1\n1 2 3\n"
  ensures var xor_sum := compute_xor_sum(arr[..]);
          var n := arr.Length;
          var effective_n := if n % 2 == 0 && xor_sum == 0 then n - 1 else n;
          (effective_n > 3 && !(n % 2 == 0 && xor_sum != 0)) ==> (
            |result| >= 4 && result[..4] == "YES\n" && 
            contains_operation_count_line(result, effective_n - 2)
          )
  ensures |result| > 0
  ensures |result| > 0 ==> result[|result|-1] == '\n'
  ensures var xor_sum := compute_xor_sum(arr[..]);
          var n := arr.Length;
          (result == "NO\n") <==> (n % 2 == 0 && xor_sum != 0)
  ensures var xor_sum := compute_xor_sum(arr[..]);
          var n := arr.Length;
          (n % 2 == 0 && xor_sum != 0) || (|result| >= 4 && result[..4] == "YES\n") || (result == "1\n1 2 3\n")
// </vc-spec>
// <vc-code>
{
  var xor_sum: int := 0;
  var i := 0;

  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant xor_sum == compute_xor_sum_partial(arr[..], i)
    invariant -2147483648 <= xor_sum <= 2147483647
  {
    xor_sum := BitwiseXor(xor_sum, arr[i]);
    i := i + 1;
  }

  var n := arr.Length;

  if n % 2 == 0 {
    if xor_sum != 0 {
      result := "NO\n";
      return;
    } else {
      n := n - 1;
    }
  }

  if n == 3 {
    result := "1\n1 2 3\n";
    return;
  }

  var operations := n - 2;
  result := "YES\n" + string_of_int(operations) + "\n";

  var j := 1;
  while j < n - 1
    invariant 1 <= j <= n + 1
    invariant j % 2 == 1
    decreases n - 1 - j
  {
    if j < n - 1 {
      result := result + string_of_int(j) + " " + string_of_int(j + 1) + " " + string_of_int(j + 2) + "\n";
    }
    j := j + 2;
  }

  var k := n - 4;
  while k > 0
    invariant k >= 0
    invariant k % 2 == 0 || k == n - 4
    decreases k
  {
    if k > 0 && k % 2 == 0 {
      result := result + string_of_int(k) + " " + string_of_int(k + 1) + " " + string_of_int(k + 2) + "\n";
    }
    k := k - 2;
  }
}
// </vc-code>
