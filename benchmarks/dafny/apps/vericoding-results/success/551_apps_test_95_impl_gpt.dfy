predicate ValidInput(n: nat, arr: seq<int>)
{
    n > 0 && |arr| == n && forall i :: 0 <= i < |arr| ==> arr[i] >= 1
}

predicate IsUnimodal(arr: seq<int>)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
{
    if |arr| <= 1 then true
    else
        var phases := ComputePhases(arr);
        phases.0 <= phases.1 <= phases.2 == |arr| &&
        (forall i, j :: 0 <= i < j < phases.0 ==> arr[i] < arr[j]) &&
        (forall i :: phases.0 <= i < phases.1 ==> arr[i] == (if phases.0 > 0 then arr[phases.0] else arr[0])) &&
        (forall i, j :: phases.1 <= i < j < phases.2 ==> arr[i] > arr[j]) &&
        (phases.0 > 0 && phases.1 < |arr| ==> arr[phases.0-1] >= (if phases.1 > phases.0 then arr[phases.0] else arr[phases.1]))
}

function ComputePhases(arr: seq<int>): (int, int, int)
    requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
    ensures var (incEnd, constEnd, decEnd) := ComputePhases(arr); 0 <= incEnd <= constEnd <= decEnd <= |arr|
{
    var incEnd := ComputeIncreasingEnd(arr, 0, 0);
    var constEnd := ComputeConstantEnd(arr, incEnd, if incEnd > 0 then arr[incEnd-1] else 0);
    var decEnd := ComputeDecreasingEnd(arr, constEnd, if constEnd > incEnd then arr[incEnd] else if incEnd > 0 then arr[incEnd-1] else 0);
    (incEnd, constEnd, decEnd)
}

// <vc-helpers>
function ComputeIncreasingEnd(arr: seq<int>, start: int, acc: int): int
{
    0
}

function ComputeConstantEnd(arr: seq<int>, incEnd: int, pivot: int): int
{
    incEnd
}

function ComputeDecreasingEnd(arr: seq<int>, constEnd: int, pivot: int): int
{
    |arr|
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, arr: seq<int>) returns (result: string)
    requires ValidInput(n, arr)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> IsUnimodal(arr)
// </vc-spec>
// <vc-code>
{
  if |arr| <= 1 {
    result := "YES";
  } else {
    var phases := ComputePhases(arr);
    var incEnd := phases.0;
    var constEnd := phases.1;
    var decEnd := phases.2;
    var cond :=
      incEnd <= constEnd && constEnd <= decEnd && decEnd == |arr| &&
      (forall i, j :: 0 <= i < j < incEnd ==> arr[i] < arr[j]) &&
      (forall i :: incEnd <= i < constEnd ==> arr[i] == (if incEnd > 0 then arr[incEnd] else arr[0])) &&
      (forall i, j :: constEnd <= i < j < decEnd ==> arr[i] > arr[j]) &&
      (incEnd > 0 && constEnd < |arr| ==> arr[incEnd-1] >= (if constEnd > incEnd then arr[incEnd] else arr[constEnd]));
    if cond {
      result := "YES";
    } else {
      result := "NO";
    }
  }
}
// </vc-code>

