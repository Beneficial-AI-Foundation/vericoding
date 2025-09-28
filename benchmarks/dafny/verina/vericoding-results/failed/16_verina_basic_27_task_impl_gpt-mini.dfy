// <vc-preamble>
datatype Option<T> = None | Some(value: T)

function CountChar(chars: seq<char>, c: char): nat
    decreases |chars|
{
    if |chars| == 0 then
        0
    else if chars[0] == c then
        1 + CountChar(chars[1..], c)
    else
        CountChar(chars[1..], c)
}

predicate HasNoDuplicatesUpTo(chars: seq<char>, endIdx: int)
    requires 0 <= endIdx <= |chars|
{
    forall i, j :: 0 <= i < j < endIdx ==> chars[i] != chars[j]
}

predicate HasNoDuplicates(chars: seq<char>)
{
    forall i, j :: 0 <= i < j < |chars| ==> chars[i] != chars[j]
}

function FirstOccurrenceIndex(chars: seq<char>, c: char): int
    requires exists i :: 0 <= i < |chars| && chars[i] == c
    ensures 0 <= FirstOccurrenceIndex(chars, c) < |chars|
    ensures chars[FirstOccurrenceIndex(chars, c)] == c
{
    if chars[0] == c then 0
    else 1 + FirstOccurrenceIndex(chars[1..], c)
}

predicate SecondOccurrenceExists(chars: seq<char>, c: char)
{
    exists i, j :: 0 <= i < j < |chars| && chars[i] == c && chars[j] == c
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Occurrence implies count >= 1 */
lemma OccurrenceImpliesCountAtLeastOne(chars: seq<char>, c: char)
  requires exists i :: 0 <= i < |chars| && chars[i] == c
  ensures CountChar(chars, c) >= 1
  decreases |chars|
{
  if |chars| == 0 {
    // unreachable because of requires
    assert false;
    return;
  }
  if chars[0] == c {
    assert CountChar(chars, c) == 1 + CountChar(chars[1..], c);
    assert CountChar(chars, c) >= 1;
  } else {
    // witness for existence must be in the tail
    OccurrenceImpliesCountAtLeastOne(chars[1..], c);
    assert CountChar(chars, c) == CountChar(chars[1..], c);
    assert CountChar(chars, c) >= 1;
  }
}

/* helper modified by LLM (iteration 5): Two occurrences imply count >= 2 */
lemma TwoOccurrencesImpliesCount(chars: seq<char>, c: char, i: int, j: int)
  requires 0 <= i < j < |chars|
  requires chars[i] == c && chars[j] == c
  ensures CountChar(chars, c) >= 2
  decreases |chars|
{
  if |chars| == 0 {
    // unreachable due to requires
    assert false;
    return;
  }
  if i == 0 {
    // occurrence at index 0 and another in the tail
    OccurrenceImpliesCountAtLeastOne(chars[1..], c);
    assert CountChar(chars, c) == 1 + CountChar(chars[1..], c);
    assert CountChar(chars, c) >= 2;
  } else {
    // both occurrences are in the tail
    TwoOccurrencesImpliesCount(chars[1..], c, i-1, j-1);
    // relate counts of chars and chars[1..]
    if chars[0] == c {
      assert CountChar(chars, c) == 1 + CountChar(chars[1..], c);
    } else {
      assert CountChar(chars, c) == CountChar(chars[1..], c);
    }
    assert CountChar(chars, c) >= 2;
  }
}

/* helper modified by LLM (iteration 5): Extend no-dup property by one element */
lemma NoDupExtend(chars: seq<char>, k: int)
  requires 0 <= k < |chars|
  requires HasNoDuplicatesUpTo(chars, k)
  requires forall i :: 0 <= i < k ==> chars[i] != chars[k]
  ensures HasNoDuplicatesUpTo(chars, k+1)
{
  // For any 0 <= i < j < k+1:
  // if j == k then chars[i] != chars[k] by requires
  // if j < k then it already holds by HasNoDuplicatesUpTo(chars, k)
  assert forall i, j :: 0 <= i < j < k+1 ==> chars[i] != chars[j];
  assert HasNoDuplicatesUpTo(chars, k+1);
}

// </vc-helpers>

// <vc-spec>
method FindFirstRepeatedChar(s: array<char>) returns (result: Option<char>)
    ensures match result {
        case Some(c) => 
            var chars := s[..];
            CountChar(chars, c) >= 2 &&
            SecondOccurrenceExists(chars, c) &&
            (exists firstIdx :: 0 <= firstIdx < |chars| && chars[firstIdx] == c &&
             exists secondIdx :: firstIdx < secondIdx < |chars| && chars[secondIdx] == c &&
             HasNoDuplicatesUpTo(chars, secondIdx))
        case None => 
            HasNoDuplicates(s[..])
    }
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): iterate to find first repeated char */
  var chars := s[..];
  var n := |chars|;
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant HasNoDuplicatesUpTo(chars, k)
  {
    var i := 0;
    while i < k
      invariant 0 <= i <= k
      invariant forall j :: 0 <= j < i ==> chars[j] != chars[k]
    {
      if chars[i] == chars[k] {
        // found a repeated character at indices i < k
        TwoOccurrencesImpliesCount(chars, chars[k], i, k);
        result := Some(chars[k]);
        return;
      }
      i := i + 1;
    }
    // no duplicate found for index k, extend the no-duplicates property
    NoDupExtend(chars, k);
    k := k + 1;
  }
  result := None;
}

// </vc-code>
