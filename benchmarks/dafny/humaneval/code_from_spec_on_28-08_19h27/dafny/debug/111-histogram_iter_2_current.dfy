type BiggestMap = map<int, int>

// <vc-helpers>
function CountOccurrences(s: seq<char>, c: char): int
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + CountOccurrences(s[1..], c)
}

function GetUniqueChars(s: seq<char>): set<char>
{
  if |s| == 0 then {}
  else {s[0]} + GetUniqueChars(s[1..])
}

function SeqToSet(s: seq<char>): set<char>
{
  set i | 0 <= i < |s| :: s[i]
}

function MaxCount(s: seq<char>, chars: set<char>): int
  requires chars <= SeqToSet(s)
  decreases chars
{
  if chars == {} then 0
  else
    var c :| c in chars;
    var rest := chars - {c};
    var count := CountOccurrences(s, c);
    if rest == {} then count
    else
      var maxRest := MaxCount(s, rest);
      if count > maxRest then count else maxRest
}

function FilterNonSpaces(s: seq<char>): seq<char>
{
  if |s| == 0 then []
  else if s[0] == ' ' then FilterNonSpaces(s[1..])
  else [s[0]] + FilterNonSpaces(s[1..])
}

lemma GetUniqueCharsSubset(s: seq<char>)
  ensures GetUniqueChars(s) <= SeqToSet(s)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def histogram(s : str) -> Dict[str, int]
Given a string representing a space separated lowercase letters, return a dictionary of the letter with the most repetition and containing the corresponding count. If several letters have the same occurrence, return all of them.
*/
// </vc-description>

// <vc-spec>
method histogram(s: string) returns (result: BiggestMap)
  ensures forall c :: c in result <==> (c as char in FilterNonSpaces(s) && 
    CountOccurrences(FilterNonSpaces(s), c as char) == MaxCount(FilterNonSpaces(s), GetUniqueChars(FilterNonSpaces(s))))
  ensures forall c :: c in result ==> result[c] == CountOccurrences(FilterNonSpaces(s), c as char)
  ensures forall c :: c in result ==> result[c] > 0
// </vc-spec>
// <vc-code>
{
  var filtered := FilterNonSpaces(s);
  if |filtered| == 0 {
    result := map[];
    return;
  }
  
  var chars := GetUniqueChars(filtered);
  GetUniqueCharsSubset(filtered);
  var maxCount := MaxCount(filtered, chars);
  
  result := map[];
  var remaining := chars;
  
  while remaining != {}
    invariant remaining <= chars
    invariant forall c :: c in result ==> c as char in filtered
    invariant forall c :: c in result ==> result[c] == CountOccurrences(filtered, c as char)
    invariant forall c :: c in result ==> result[c] == maxCount
    decreases remaining
  {
    var c :| c in remaining;
    var count := CountOccurrences(filtered, c);
    if count == maxCount {
      result := result[c as int := count];
    }
    remaining := remaining - {c};
  }
}
// </vc-code>
