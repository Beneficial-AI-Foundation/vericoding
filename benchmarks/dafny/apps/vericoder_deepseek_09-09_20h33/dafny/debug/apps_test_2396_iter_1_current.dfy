predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidOutput(result: seq<int>, input: string)
{
    |result| >= 0 &&
    (forall i :: 0 <= i < |result| ==> result[i] >= 1) &&
    (forall i :: 0 <= i < |result| ==> result[i] <= |result|)
}

// <vc-helpers>
lemma CountLemma(s: string, c: char, start: end: int)
  requires 0 <= start <= end <= |s|
  ensures count(s, c, start, end) >= 0
{
}

function count(s: string, c: char, start: int, end: int): int
  requires 0 <= start <= end <= |s|
  decreases end - start
{
  if start == end then 0
  else (if s[start] == c then 1 else 0) + count(s, c, start + 1, end)
}

lemma CountProperty(s: string, c: char, start: end: int)
  requires 0 <= start < end <= |s|
  ensures count(s, c, start, end) == (if s[start] == c then 1 else 0) + count(s, c, start + 1, end)
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: seq<int>)
    requires ValidInput(input)
    ensures ValidOutput(result, input)
// </vc-spec>
// <vc-code>
{
    var n := |input|;
    result := [];
    var freq : map<int, int> := map[];
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] >= 1 && result[j] <= i
        invariant forall k :: k in freq.Keys ==> 1 <= k <= i && freq[k] >= 1
        invariant forall k :: k in freq.Keys ==> freq[k] == count(input, input[i-1], 0, i)
    {
        var currentChar := input[i];
        var currentCount := count(input, currentChar, 0, i);
        result := result + [currentCount + 1];
        freq := freq[currentCount + 1 := currentCount + 1];
        i := i + 1;
    }
}
// </vc-code>

