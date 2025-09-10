predicate ValidInput(n: int, a: int, x: seq<int>)
{
    n > 0 && 1 <= a <= n && |x| == n && 
    forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
}

function SumCriminalsCaught(n: int, a_idx: int, x: seq<int>, distance: int): int
    requires n > 0
    requires 0 <= a_idx < n
    requires |x| == n
    requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    requires distance >= 1
    decreases n + 1 - distance
    ensures SumCriminalsCaught(n, a_idx, x, distance) >= 0
{
    if distance > n then 0
    else
        var le := a_idx - distance;
        var rg := a_idx + distance;
        var le_valid := le >= 0 && le < n;
        var rg_valid := rg >= 0 && rg < n;
        var current_caught :=
            if !le_valid && !rg_valid then 0
            else if le_valid && !rg_valid then x[le]
            else if !le_valid && rg_valid then x[rg]
            else if le_valid && rg_valid && x[le] == 1 && x[rg] == 1 then 2
            else 0;
        if !le_valid && !rg_valid then current_caught
        else current_caught + SumCriminalsCaught(n, a_idx, x, distance + 1)
}

function TotalCriminalsCaught(n: int, a: int, x: seq<int>): int
    requires ValidInput(n, a, x)
{
    x[a-1] + SumCriminalsCaught(n, a-1, x, 1)
}

// <vc-helpers>
lemma SumCriminalsCaughtTerminates(n: int, a_idx: int, x: seq<int>, distance: int)
  requires n > 0
  requires 0 <= a_idx < n
  requires |x| == n
  requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
  requires distance >= 1
  ensures SumCriminalsCaught(n, a_idx, x, distance) >= 0
{
  // Termination is ensured by the decreases clause in the function definition
}

lemma TotalCriminalsCaughtNonNegative(n: int, a: int, x: seq<int>)
  requires ValidInput(n, a, x)
  ensures TotalCriminalsCaught(n, a, x) >= 0
{
}

// Helper function to compute partial sum
function SumCriminalsCaughtPartial(n: int, a_idx: int, x: seq<int>, start: int, end: int): int
  requires n > 0
  requires 0 <= a_idx < n
  requires |x| == n
  requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
  requires start >= 1 && end >= start - 1
  decreases end + 1 - start
{
  if start > end then 0
  else
    var le := a_idx - start;
    var rg := a_idx + start;
    var le_valid := le >= 0 && le < n;
    var rg_valid := rg >= 0 && rg < n;
    var current_caught :=
      if !le_valid && !rg_valid then 0
      else if le_valid && !rg_valid then x[le]
      else if !le_valid && rg_valid then x[rg]
      else if le_valid && rg_valid && x[le] == 1 && x[rg] == 1 then 2
      else if le_valid && rg_valid && x[le] == 1 then 1
      else if le_valid && rg_valid && x[rg] == 1 then 1
      else 0;
    current_caught + SumCriminalsCaughtPartial(n, a_idx, x, start + 1, end)
}

lemma SumCriminalsCaughtEqualsPartial(n: int, a_idx: int, x: seq<int>, distance: int)
  requires n > 0
  requires 0 <= a_idx < n
  requires |x| == n
  requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
  requires distance >= 1
  ensures SumCriminalsCaught(n, a_idx, x, distance) == SumCriminalsCaughtPartial(n, a_idx, x, distance, n)
{
  if distance > n {
  } else {
    var le := a_idx - distance;
    var rg := a_idx + distance;
    var le_valid := le >= 0 && le < n;
    var rg_valid := rg >= 0 && rg < n;
    SumCriminalsCaughtEqualsPartial(n, a_idx, x, distance + 1);
  }
}

lemma SumCriminalsCaughtPartialBase(n: int, a_idx: int, x: seq<int>, start: int)
  requires n > 0
  requires 0 <= a_idx < n
  requires |x| == n
  requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
  requires start >= 1
  ensures SumCriminalsCaughtPartial(n, a_idx, x, start, start - 1) == 0
{
}

lemma SumCriminalsCaughtPartialExtend(n: int, a_idx: int, x: seq<int>, start: int, end: int)
  requires n > 0
  requires 0 <= a_idx < n
  requires |x| == n
  requires forall i :: 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
  requires start >= 1 && end >= start
  ensures SumCriminalsCaughtPartial(n, a_idx, x, start, end) == 
          SumCriminalsCaughtPartial(n, a_idx, x, start, end - 1) +
          (if a_idx - end >= 0 && a_idx - end < n && x[a_idx - end] == 1 then 1 else 0) +
          (if a_idx + end >= 0 && a_idx + end < n && x[a_idx + end] == 1 && end != 0 then 1 else 0)
{
  if start < end {
    SumCriminalsCaughtPartialExtend(n, a_idx, x, start, end - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, x: seq<int>) returns (result: int)
    requires ValidInput(n, a, x)
    ensures result >= 0
    ensures result == TotalCriminalsCaught(n, a, x)
// </vc-spec>
// <vc-code>
{
  result := x[a-1];
  var d := 1;
  var a_idx := a - 1;
  while d <= n
    invariant 1 <= d <= n + 1
    invariant result >= 0
    invariant result == x[a_idx] + SumCriminalsCaughtPartial(n, a_idx, x, 1, d-1)
    decreases n - d + 1
  {
    var le := a_idx - d;
    var rg := a_idx + d;
    var current_caught := 0;
    
    if le >= 0 && le < n && x[le] == 1 {
      current_caught := current_caught + 1;
    }
    if rg >= 0 && rg < n && x[rg] == 1 {
      current_caught := current_caught + 1;
    }
    
    // Update invariant
    result := result + current_caught;
    d := d + 1;
    
    // Prove the invariant holds for the next iteration
    if d <= n {
      assert SumCriminalsCaughtPartial(n, a_idx, x, 1, d-1) == 
             SumCriminalsCaughtPartial(n, a_idx, x, 1, d-2) + current_caught;
    }
  }
  assert SumCriminalsCaughtPartial(n, a_idx, x, 1, n) == SumCriminalsCaught(n, a_idx, x, 1);
}
// </vc-code>

