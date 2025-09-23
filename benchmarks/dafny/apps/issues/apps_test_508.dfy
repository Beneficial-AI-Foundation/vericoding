// <vc-preamble>
predicate ValidInput(n: int, a: int) {
  3 <= n <= 100000 && 1 <= a <= 180
}

predicate ValidOutput(v1: int, v2: int, v3: int, n: int) {
  1 <= v1 <= n && 1 <= v2 <= n && 1 <= v3 <= n &&
  v1 != v2 && v2 != v3 && v1 != v3
}

function AngleDifference(k: int, a: int, n: int): int
  requires 1 <= k < n - 1 && 3 <= n
{
  var angle_times_n := k * 180;
  var target_times_n := a * n;
  if target_times_n >= angle_times_n then target_times_n - angle_times_n 
  else angle_times_n - target_times_n
}

predicate IsOptimal(k: int, a: int, n: int)
  requires 1 <= k < n - 1 && 3 <= n
{
  forall i :: 1 <= i < n - 1 ==> AngleDifference(k, a, n) <= AngleDifference(i, a, n)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int) returns (v1: int, v2: int, v3: int)
  requires ValidInput(n, a)
  ensures ValidOutput(v1, v2, v3, n)
  ensures exists k :: 1 <= k < n - 1 && v1 == 2 && v2 == 1 && v3 == k + 2 && IsOptimal(k, a, n)
// </vc-spec>
// <vc-code>
{
  var res := 1;
  var i := 2;
  while i < n - 1
    invariant 1 <= res < n - 1
    invariant 2 <= i <= n - 1
    invariant forall j :: 1 <= j < i ==> AngleDifference(res, a, n) <= AngleDifference(j, a, n)
  {
    var current_diff := AngleDifference(res, a, n);
    var new_diff := AngleDifference(i, a, n);
    if current_diff > new_diff {
      res := i;
    }
    i := i + 1;
  }
  
  assert 1 <= res < n - 1;
  assert forall j :: 1 <= j < n - 1 ==> AngleDifference(res, a, n) <= AngleDifference(j, a, n);
  assert IsOptimal(res, a, n);
  
  v1 := 2;
  v2 := 1;
  v3 := res + 2;
}
// </vc-code>
