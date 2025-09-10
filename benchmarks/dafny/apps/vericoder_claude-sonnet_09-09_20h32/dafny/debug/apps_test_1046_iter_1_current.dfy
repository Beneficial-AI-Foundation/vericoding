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
lemma CountOccurrencesNonNegative(s: seq<int>, x: int)
  ensures CountOccurrences(s, x) >= 0
{
}

lemma CountOccurrencesEmpty(x: int)
  ensures CountOccurrences([], x) == 0
{
}

lemma CountOccurrencesProperties(s: seq<int>, x: int)
  ensures CountOccurrences(s, x) >= 0
  ensures CountOccurrences(s, x) <= |s|
{
  if |s| == 0 {
  } else {
    CountOccurrencesProperties(s[1..], x);
  }
}

lemma FilterPositivePreservesElements(s: seq<int>)
  ensures forall i :: 0 <= i < |FilterPositive(s)| ==> exists j :: 0 <= j < |s| && s[j] == FilterPositive(s)[i]
{
  if |s| == 0 {
  } else {
    FilterPositivePreservesElements(s[1..]);
  }
}

lemma RemoveAllOccurrencesCorrect(s: seq<int>, x: int)
  ensures CountOccurrences(RemoveAllOccurrences(s, x), x) == 0
  ensures forall y :: y != x ==> CountOccurrences(RemoveAllOccurrences(s, x), y) == CountOccurrences(s, y)
{
  if |s| == 0 {
  } else {
    RemoveAllOccurrencesCorrect(s[1..], x);
  }
}

lemma CountPairsCorrectness(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures CountPairsHelper(s) >= 0
{
  if |s| <= 1 {
  } else {
    var count := CountOccurrences(s, s[0]);
    var remaining := RemoveAllOccurrences(s, s[0]);
    RemoveAllOccurrencesCorrect(s, s[0]);
    CountPairsCorrectness(remaining);
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
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> sessions[j] >= 0
  {
    if sessions[i] > 0 {
      var count := 0;
      var j := 0;
      while j < n
        invariant 0 <= j <= n
        invariant count == CountOccurrences(sessions[0..j], sessions[i])
        invariant count >= 0
      {
        if sessions[j] == sessions[i] {
          count := count + 1;
        }
        j := j + 1;
      }
      
      if count > 2 {
        return -1;
      }
    }
    i := i + 1;
  }
  
  result := CountPairs(sessions);
}
// </vc-code>

