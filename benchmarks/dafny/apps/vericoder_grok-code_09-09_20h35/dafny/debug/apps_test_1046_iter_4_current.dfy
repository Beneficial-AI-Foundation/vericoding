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
// <vc-helpers>
// No changes needed in helpers to fix the verification errors.
// </vc-helpers>
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
  var hasExcess := false;
  var numPairs := 0;
  var counts: map<int, int> := map[];
  var keys: set<int> := {};
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant forall k :: k in keys ==> 0 < k && counts[k] == CountOccurrences(sessions[..i], k)
    invariant forall k :: 0 < k && 0 <= CountOccurrences(sessions[..i], k) && CountOccurrences(sessions[..i], k) > 0 ==> k in keys
  {
    var id := sessions[i];
    if id > 0 {
      if id !in keys {
        keys := keys + {id};
        counts := counts[id := 1];
      } else {
        counts := counts[id := counts[id] + 1];
      }
    }
  }
  var tempKeys := keys;
  var processed := {};
  while tempKeys != {}
    invariant tempKeys * processed == {}
    invariant tempKeys + processed == keys
    invariant hasExcess == exists k :: k in processed && counts[k] > 2
    invariant numPairs == |{k : int | k in processed && counts[k] == 2}|
  {
    var k :| k in tempKeys;
    tempKeys := tempKeys - {k};
    processed := processed + {k};
    if counts[k] > 2 {
      hasExcess := true;
    }
    if counts[k] == 2 {
      numPairs := numPairs + 1;
    }
  }
  if hasExcess {
    result := -1;
  } else {
    result := numPairs;
  }
}
// </vc-code>

