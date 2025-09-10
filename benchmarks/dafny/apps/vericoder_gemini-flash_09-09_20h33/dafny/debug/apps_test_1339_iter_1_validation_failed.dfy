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

// <vc-helpers>
function findMinLeft(segments: seq<(int, int)>): int
  requires |segments| > 0
  ensures forall i :: 0 <= i < |segments| ==> findMinLeft(segments) <= segments[i].0
  ensures exists i :: 0 <= i < |segments| && findMinLeft(segments) == segments[i].0
{
  var minL := segments[0].0;
  for i := 1 to |segments|-1
    invariant 1 <= i <= |segments|
    invariant forall j :: 0 <= j < i ==> minL <= segments[j].0
    invariant exists j :: 0 <= j < i && minL == segments[j].0
  {
    if segments[i].0 < minL {
      minL := segments[i].0;
    }
  }
  return minL;
}

function findMaxRight(segments: seq<(int, int)>): int
  requires |segments| > 0
  ensures forall i :: 0 <= i < |segments| ==> findMaxRight(segments) >= segments[i].1
  ensures exists i :: 0 <= i < |segments| && findMaxRight(segments) == segments[i].1
{
  var maxR := segments[0].1;
  for i := 1 to |segments|-1
    invariant 1 <= i <= |segments|
    invariant forall j :: 0 <= j < i ==> maxR >= segments[j].1
    invariant exists j :: 0 <= j < i && maxR == segments[j].1
  {
    if segments[i].1 > maxR {
      maxR := segments[i].1;
    }
  }
  return maxR;
}
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
{
  var minL := findMinLeft(segments);
  var maxR := findMaxRight(segments);

  var found_index := -1;
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant found_index == -1 || (0 <= found_index < i &&
                HasMinLeftAndMaxRight(segments, found_index) &&
                CoversAll(segments, found_index))
  {
    if segments[i].0 == minL && segments[i].1 == maxR {
      found_index := i;
      break;
    }
  }

  if found_index != -1 {
    result := found_index + 1;
    // Prove postconditions for result != -1
    var idx := result - 1;
    assert idx == found_index;

    // Prove HasMinLeftAndMaxRight(segments, idx)
    // From loop, we know segments[idx].0 == minL and segments[idx].1 == maxR
    forall j | 0 <= j < n
      ensures segments[idx].0 <= segments[j].0
    {
      assert minL <= segments[j].0 by {
        reveal findMinLeft();
        assert findMinLeft(segments) <= segments[j].0;
      }
    }
    forall j | 0 <= j < n
      ensures segments[idx].1 >= segments[j].1
    {
      assert maxR >= segments[j].1 by {
        reveal findMaxRight();
        assert findMaxRight(segments) >= segments[j].1;
      }
    }

    // Prove CoversAll(segments, idx)
    forall j | 0 <= j < n
      ensures segments[idx].0 <= segments[j].0 && segments[j].1 <= segments[idx].1
    {
      assert segments[idx].0 == minL;
      assert segments[idx].1 == maxR;
      assert minL <= segments[j].0 by {
        reveal findMinLeft();
        assert findMinLeft(segments) <= segments[j].0;
      }
      assert segments[j].1 <= maxR by {
        reveal findMaxRight();
        assert findMaxRight(segments) >= segments[j].1;
      }
    }

  } else {
    result := -1;
    // Prove postconditions for result == -1
    // Assume for contradiction that there exists such an `i`
    // Let k be such an index
    // Then segments[k].0 == minL and segments[k].1 == maxR (by properties of HasMinLeftAndMaxRight)
    // However, the loop would have found `k` and set `found_index := k`.
    // This contradicts `found_index == -1`.
  }
}
// </vc-code>

