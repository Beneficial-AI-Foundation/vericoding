// <vc-preamble>
predicate ValidInput(n: int, segments: seq<(int, int)>)
{
    n >= 1 && |segments| == n && 
    forall i :: 0 <= i < n ==> segments[i].0 <= segments[i].1
}

predicate CoversAll(segments: seq<(int, int)>, idx: int)
{
    0 <= idx < |segments| &&
    forall j :: 0 <= j < |segments| ==> 
        segments[idx].0 <= segments[j].0 && segments[j].1 <= segments[idx].1
}

predicate HasMinLeftAndMaxRight(segments: seq<(int, int)>, idx: int)
{
    0 <= idx < |segments| &&
    (forall j :: 0 <= j < |segments| ==> segments[idx].0 <= segments[j].0) &&
    (forall j :: 0 <= j < |segments| ==> segments[idx].1 >= segments[j].1)
}

function MinLeft(segments: seq<(int, int)>): int
    requires |segments| > 0
{
    if |segments| == 1 then segments[0].0
    else if segments[0].0 <= MinLeft(segments[1..]) then segments[0].0
    else MinLeft(segments[1..])
}

function MaxRight(segments: seq<(int, int)>): int
    requires |segments| > 0
{
    if |segments| == 1 then segments[0].1
    else if segments[0].1 >= MaxRight(segments[1..]) then segments[0].1
    else MaxRight(segments[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper predicate `HasMinLeftAndMaxRightAndCovers` is removed as the original error indicates a problem with the postcondition `HasMinLeftAndMaxRight(segments, i)` when `result == -1`. The previous helper was causing confusion. Reverted to simpler `HasMinLeftAndMaxRight` for clarity. */
// </vc-helpers>

// <vc-spec>
method solve(n: int, segments: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, segments)
    ensures result == -1 || (1 <= result <= n)
    ensures result != -1 ==> 
        (var idx := result - 1;
         HasMinLeftAndMaxRight(segments, idx) &&
         CoversAll(segments, idx))
    ensures result == -1 ==> 
        !(exists i :: 0 <= i < n && HasMinLeftAndMaxRight(segments, i))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous helper predicate `HasMinLeftAndMaxRightAndCovers` was not aligned with the postcondition, causing a verification error specifically when `result == -1`. This revision simplifies the loop condition to directly check `HasMinLeftAndMaxRight` and `CoversAll` as per method postconditions, ensuring the `result == -1` postcondition is verifiable by checking *both* conditions when a candidate is found. The `return` statement immediately exits if a valid segment is identified. */
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> !(HasMinLeftAndMaxRight(segments, k) && CoversAll(segments, k))
  {
    if HasMinLeftAndMaxRight(segments, i) && CoversAll(segments, i) {
      return i + 1;
    }
    i := i + 1;
  }
  return -1;
}
// </vc-code>
