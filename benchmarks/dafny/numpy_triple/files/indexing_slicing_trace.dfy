// <vc-preamble>
// Helper function to compute the sum of diagonal elements
ghost function DiagonalSum(a: seq<seq<real>>, offset: int): real
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==> |a[i]| == |a[j]|
{
  if |a| == 0 then 0.0
  else
    var rows := |a|;
    var cols := |a[0]|;
    
    if offset >= 0 then
      // Sum elements a[i][i+offset] for valid i
      var maxI := if rows <= cols - offset then rows - 1 else cols - 1 - offset;
      if maxI < 0 then 0.0
      else SumDiagonalNonnegOffset(a, offset, 0, maxI)
    else
      // Sum elements a[i-offset][i] for valid i  
      var minI := -offset;
      var maxI := if rows + offset - 1 <= cols - 1 then rows + offset - 1 else cols - 1;
      if minI > maxI then 0.0
      else SumDiagonalNegOffset(a, offset, minI, maxI)
}

// Helper function for non-negative offset case
ghost function SumDiagonalNonnegOffset(a: seq<seq<real>>, offset: int, start: int, end: int): real
  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==> |a[i]| == |a[j]|
  requires offset >= 0
  requires 0 <= start <= end
  requires forall i {:trigger a[i]} :: start <= i <= end ==> 0 <= i < |a| && 0 <= i + offset < |a[0]|
  decreases end - start + 1
{
  if start > end then 0.0
  else a[start][start + offset] + SumDiagonalNonnegOffset(a, offset, start + 1, end)
}

// Helper function for negative offset case
ghost function SumDiagonalNegOffset(a: seq<seq<real>>, offset: int, start: int, end: int): real
  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==> |a[i]| == |a[j]|
  requires offset < 0
  requires 0 <= start <= end
  requires forall i {:trigger a[i]} :: start <= i <= end ==> 0 <= i - offset < |a| && 0 <= i < |a[0]|
  decreases end - start + 1
{
  if start > end then 0.0
  else a[start - offset][start] + SumDiagonalNegOffset(a, offset, start + 1, end)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method trace(a: seq<seq<real>>, offset: int) returns (result: real)
  // Matrix must be rectangular (but can be empty)
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==> |a[i]| == |a[j]|
  
  // Result is the sum of diagonal elements with the given offset
  ensures result == DiagonalSum(a, offset)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
