function CountOccurrences(s: seq<int>, x: int): int
  ensures CountOccurrences(s, x) >= 0
{
  if |s| == 0 then 0
  else (if s[0] == x then 1 else 0) + CountOccurrences(s[1..], x)
}

function CountPairs(s: seq<int>): int
  ensures CountPairs(s) >= 0
{
  var positive_sessions := FilterPositive(s);
  CountPairsHelper(positive_sessions)
}

function FilterPositive(s: seq<int>): seq<int>
  ensures forall i :: 0 <= i < |FilterPositive(s)| ==> FilterPositive(s)[i] > 0
{
  if |s| == 0 then []
  else if s[0] > 0 then [s[0]] + FilterPositive(s[1..])
  else FilterPositive(s[1..])
}

function CountPairsHelper(s: seq<int>): int
  decreases |s|
  ensures CountPairsHelper(s) >= 0
{
  if |s| <= 1 then 0
  else 
    var count := CountOccurrences(s, s[0]);
    var remaining := RemoveAllOccurrences(s, s[0]);
    (if count == 2 then 1 else 0) + CountPairsHelper(remaining)
}

function RemoveAllOccurrences(s: seq<int>, x: int): seq<int>
  ensures |RemoveAllOccurrences(s, x)| <= |s|
{
  if |s| == 0 then []
  else if s[0] == x then RemoveAllOccurrences(s[1..], x)
  else [s[0]] + RemoveAllOccurrences(s[1..], x)
}

predicate ExistsIndex(s: seq<int>, x: int)
{
  exists i :: 0 <= i < |s| && s[i] == x
}

// <vc-helpers>
lemma IfNotExistsThenZero(s: seq<int>, id: int)
  requires id > 0
  requires !ExistsIndex(s, id)
  ensures CountOccurrences(s, id) == 0
  decreases |s|
{
  if |s| == 0 {
    assert CountOccurrences(s, id) == 0;
    return;
  }
  if s[0] == id {
    // contradicts !ExistsIndex(s,id)
    assert false;
  }
  // CountOccurrences(s,id) == (if s[0]==id then 1 else 0) + CountOccurrences(s[1..], id)
  assert CountOccurrences(s, id) == CountOccurrences(s[1..], id);
  // show !ExistsIndex on the tail
  if ExistsIndex(s[1..], id) {
    var j :| 0 <= j < |s[1..]| && s[1 + j] == id;
    assert 0 <= 1 + j < |s|;
    assert s[1 + j] == id;
    assert ExistsIndex(s, id);
    assert false;
  }
  // recursive step
  IfNotExistsThenZero(s[1..], id);
  assert CountOccurrences(s, id) == 0;
}

lemma CountsFromIndexedToAll(s: seq<int>)
  requires forall k :: 0 <= k < |s| && s[k] > 0 ==> CountOccurrences(s, s[k]) <= 2
  ensures forall id :: id > 0 ==> CountOccurrences(s, id) <= 2
{
  // Prove the property for an arbitrary positive id.
  forall id | id > 0
    {:trigger CountOccurrences(s, id)}
  {
    ensures CountOccurrences(s, id) <= 2;
    if ExistsIndex(s, id) {
      var k :| 0 <= k < |s| && s[k] == id;
      assert s[k] > 0;
      assert CountOccurrences(s, id) == CountOccurrences(s, s[k]);
      assert CountOccurrences(s, id) <= 2;
    } else {
      IfNotExistsThenZero(s, id);
      assert CountOccurrences(s, id) == 0;
      assert CountOccurrences(s, id) <= 2;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, sessions: seq<int>) returns (result: int)
  requires n >= 1
  requires |sessions| == n
  requires forall i :: 0 <= i < |sessions| ==> sessions[i] >= 0
  ensures result == -1 || result >= 0
  ensures result == -1 ==> exists id :: id > 0 && CountOccurrences(sessions, id) > 2
  ensures result >= 0 ==> forall id :: id > 0 ==> CountOccurrences(sessions, id) <= 2
  ensures result >= 0 ==> result == CountPairs(sessions)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |sessions|
    invariant 0 <= i <= |sessions|
    invariant forall k :: 0 <= k < i && sessions[k] > 0 ==> CountOccurrences(sessions, sessions[k]) <= 2
    decreases |sessions| - i
  {
    if sessions[i] > 0 {
      var c := CountOccurrences(sessions, sessions[i]);
      if c > 2 {
        result := -1;
        return;
      }
    }
    i := i + 1;
  }
  // Use lemma to conclude the required global property from the loop invariant
  CountsFromIndexedToAll(sessions);
  result := CountPairs(sessions);
}
// </vc-code>

