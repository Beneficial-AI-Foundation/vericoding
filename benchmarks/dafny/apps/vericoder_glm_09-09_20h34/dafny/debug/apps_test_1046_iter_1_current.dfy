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
lemma CountPairsHelperProperties(s: seq<int>)
  ensures CountPairsHelper(s) >= 0
  ensures CountPairsHelper(s) <= |s| / 2
{
  if |s| <= 1 {
  } else {
    var count := CountOccurrences(s, s[0]);
    var remaining := RemoveAllOccurrences(s, s[0]);
    calc {
      CountPairsHelper(s);
      (if count == 2 then 1 else 0) + CountPairsHelper(remaining);
    ==  { CountPairsHelperProperties(remaining); }
      (if count == 2 then 1 else 0) + (CountPairsHelper(remaining) >= 0 && CountPairsHelper(remaining) <= |remaining| / 2);
    }
  }
}

lemma RemoveAllOccurrencesEffect(s: seq<int>, x: int)
  ensures !ExistsIndex(RemoveAllOccurrences(s, x), x)
  ensures forall y :: y != x ==> CountOccurrences(RemoveAllOccurrences(s, x), y) == CountOccurrences(s, y)
  ensures CountOccurrences(s, x) + CountOccurrences(RemoveAllOccurrences(s, x), x) == CountOccurrences(s, x)
{
  if |s| == 0 {
  } else if s[0] == x {
    RemoveAllOccurrencesEffect(s[1..], x);
  } else {
    RemoveAllOccurrencesEffect(s[1..], x);
  }
}

lemma CountPairsCorrectness(s: seq<int>)
  ensures CountPairs(s) == CountPairsHelper(FilterPositive(s))
  ensures CountPairs(s) >= 0
{
  CountPairsHelperProperties(FilterPositive(s));
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
  var positive_sessions := FilterPositive(sessions);
  
  if CountPairsHelper(positive_sessions) >= 0 {
    return CountPairsHelper(positive_sessions);
  } else {
    return -1;
  }
}
// </vc-code>

