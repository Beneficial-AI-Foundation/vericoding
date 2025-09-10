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
lemma RemoveAllOccurrencesPreservesPositive(s: seq<int>, x: int)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures forall i :: 0 <= i < |RemoveAllOccurrences(s, x)| ==> RemoveAllOccurrences(s, x)[i] > 0
{
  if |s| == 0 {
  } else if s[0] == x {
    RemoveAllOccurrencesPreservesPositive(s[1..], x);
  } else {
    RemoveAllOccurrencesPreservesPositive(s[1..], x);
  }
}

lemma CountOccurrencesRemoveAll(s: seq<int>, x: int)
  ensures CountOccurrences(RemoveAllOccurrences(s, x), x) == 0
{
  if |s| == 0 {
  } else if s[0] == x {
    CountOccurrencesRemoveAll(s[1..], x);
  } else {
    CountOccurrencesRemoveAll(s[1..], x);
  }
}

lemma FilterPositiveIsPositive(s: seq<int>)
  ensures forall i :: 0 <= i < |FilterPositive(s)| ==> FilterPositive(s)[i] > 0
{
}

lemma CountPairsHelperCorrectness(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  decreases |s|
  ensures CountPairsHelper(s) >= 0
  ensures CountPairsHelper(s) == CountPairs(s)
{
  if |s| <= 1 {
  } else {
    var count := CountOccurrences(s, s[0]);
    var remaining := RemoveAllOccurrences(s, s[0]);
    RemoveAllOccurrencesPreservesPositive(s, s[0]);
    CountOccurrencesRemoveAll(s, s[0]);
    CountPairsHelperCorrectness(remaining);
  }
}

lemma CountOccurrencesSlice(s: seq<int>, x: int, i: int)
  requires 0 <= i <= |s|
  ensures CountOccurrences(s[0..i], x) >= 0
{
}

lemma CountPairsSlice(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures CountPairs(s[0..i]) >= 0
{
}

lemma CountOccurrencesMonotonic(s: seq<int>, x: int, i: int, j: int)
  requires 0 <= i <= j <= |s|
  ensures CountOccurrences(s[0..i], x) <= CountOccurrences(s[0..j], x)
{
}

lemma CountOccurrencesSplit(s: seq<int>, x: int, i: int)
  requires 0 <= i < |s|
  ensures CountOccurrences(s[0..i+1], x) == CountOccurrences(s[0..i], x) + (if s[i] == x then 1 else 0)
{
}

lemma CountPairsSplit(s: seq<int>, i: int)
  requires 0 <= i < |s|
  requires forall id :: id > 0 ==> CountOccurrences(s[0..i], id) <= 2
  ensures CountPairs(s[0..i+1]) == CountPairs(s[0..i]) + (if s[i] > 0 && CountOccurrences(s[0..i], s[i]) == 1 then 1 else 0)
{
}
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
  var count := 0;
  var i := 0;
  var seen : set<int> := {};
  
  while i < |sessions|
    invariant 0 <= i <= |sessions|
    invariant forall x :: x in seen ==> 0 < x && CountOccurrences(sessions[0..i], x) <= 2
    invariant forall x :: x > 0 && x !in seen ==> CountOccurrences(sessions[0..i], x) <= 1
    invariant count >= 0
    invariant count == CountPairs(sessions[0..i])
  {
    var id := sessions[i];
    if id > 0 {
      var old_count := CountOccurrences(sessions[0..i], id);
      CountOccurrencesSplit(sessions, id, i);
      var new_count := old_count + 1;
      
      if new_count > 2 {
        result := -1;
        return;
      }
      
      if id !in seen {
        if new_count == 2 {
          count := count + 1;
        }
        seen := seen + {id};
      } else if new_count == 2 {
        count := count + 1;
      }
    }
    i := i + 1;
  }
  
  // Check if any ID appears more than twice in the entire sequence
  var j := 0;
  while j < |sessions|
    invariant 0 <= j <= |sessions|
    invariant forall x :: x > 0 ==> CountOccurrences(sessions[0..j], x) <= 2
  {
    var id := sessions[j];
    if id > 0 {
      if CountOccurrences(sessions, id) > 2 {
        result := -1;
        return;
      }
    }
    j := j + 1;
  }
  
  result := count;
}
// </vc-code>

