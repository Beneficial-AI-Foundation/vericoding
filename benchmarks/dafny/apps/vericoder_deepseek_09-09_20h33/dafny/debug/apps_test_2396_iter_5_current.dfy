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
lemma CountLemma(s: string, c: char, start: int, end: int)
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

lemma CountProperty(s: string, c: char, start: int, end: int)
  requires 0 <= start < end <= |s|
  ensures count(s, c, start, end) == (if s[start] == c then 1 else 0) + count(s, c, start + 1, end)
{
}

lemma CountPositivity(s: string, c: char, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures count(s, c, start, end) >= 0
{
}

lemma CountUpperBound(s: string, c: char, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures count(s, c, start, end) <= end - start
{
  if start == end {
  } else {
    CountUpperBound(s, c, start + 1, end);
  }
}
// </vc-helpers>
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
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] >= 1 && result[j] <= i
    {
        var currentChar := input[i];
        var currentCount := count(input, currentChar, 0, i);
        CountUpperBound(input, currentChar, 0, i);
        var newVal := currentCount + 1;
        result := result + [newVal];
        CountPositivity(input, currentChar, 0, i);
        assert newVal >= 1;
        assert newVal <= i + 1;
        i := i + 1;
    }
}
// </vc-code>

