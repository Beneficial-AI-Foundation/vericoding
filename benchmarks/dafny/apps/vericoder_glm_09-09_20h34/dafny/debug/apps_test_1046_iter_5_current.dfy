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
lemma RemoveAllOccurrencesEffect(s: seq<int>, x: int)
  ensures |RemoveAllOccurrences(s, x)| == |s| - CountOccurrences(s, x)
{
  if |s| == 0 {
  } else {
    RemoveAllOccurrencesEffect(s[1..], x);
    if s[0] == x {
      calc {
        |RemoveAllOccurrences(s, x)|
        == |RemoveAllOccurrences(s[1..], x)|;
        == |s[1..]| - CountOccurrences(s[1..], x);
        == (|s| - 1) - CountOccurrences(s[1..], x);
        == |s| - (1 + CountOccurrences(s[1..], x));
        == |s| - CountOccurrences(s, x);
      }
    } else {
      calc {
        |RemoveAllOccurrences(s, x)|
        == 1 + |RemoveAllOccurrences(s[1..], x)|;
        == 1 + (|s[1..]| - CountOccurrences(s[1..], x));
        == 1 + (|s| - 1 - CountOccurrences(s[1..], x));
        == |s| - CountOccurrences(s[1..], x);
        == |s| - CountOccurrences(s, x);
      }
    }
  }
}

lemma CountPairsHelperProperties(s: seq<int>)
  ensures CountPairsHelper(s) >= 0
  ensures CountPairsHelper(s) <= |s| / 2
{
  if |s| <= 1 {
  } else {
    var count := CountOccurrences(s, s[0]);
    var remaining := RemoveAllOccurrences(s, s[0]);
    RemoveAllOccurrencesEffect(s, s[0]);
    assert |remaining| == |s| - count;
    CountPairsHelperProperties(remaining);
    if count == 2 {
      calc {
        CountPairsHelper(s)
        == 1 + CountPairsHelper(remaining);
        <= 1 + |remaining| / 2;
        == 1 + (|s| - count) / 2;
        == 1 + (|s| - 2) / 2;
        == 1 + |s|/2 - 1;
        == |s|/2;
      }
    } else {
      calc {
        CountPairsHelper(s)
        == CountPairsHelper(remaining);
        <= |remaining| / 2;
        == (|s| - count) / 2;
        <= |s| / 2;
      }
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
  if exists id: int :: id>0 && CountOccurrences(sessions, id)>2 {
    return -1;
  } else {
    assert forall id: int :: id>0 ==> CountOccurrences(sessions, id) <= 2;
    return CountPairs(sessions);
  }
}
// </vc-code>

