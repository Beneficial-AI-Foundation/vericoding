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
/* helper modified by LLM (iteration 5): Contains predicate over a sequence */
function Contains(chars: seq<char>, c: char): bool
{
  exists i :: 0 <= i < |chars| && chars[i] == c
}

/* helper modified by LLM (iteration 5): Equivalence for Contains on a prefix */
lemma ContainsPrefixEquiv(chars: seq<char>, c: char, i: int)
  requires 0 <= i <= |chars|
  ensures Contains(chars[..i], c) <==> (exists k :: 0 <= k < i && chars[k] == c)
{
  if Contains(chars[..i], c) {
    var k: int :| 0 <= k < |chars[..i]| && chars[..i][k] == c;
    assert 0 <= k < i;
    assert chars[k] == c;
  }
  if (exists k2 :: 0 <= k2 < i && chars[k2] == c) {
    var k2: int :| 0 <= k2 < i && chars[k2] == c;
    assert 0 <= k2 < |chars[..i]|;
    assert chars[..i][k2] == c;
  }
}

/* helper modified by LLM (iteration 5): Extend no-duplicates invariant by one element */
lemma ExtendNoDuplicates(chars: seq<char>, i: int)
  requires 0 <= i < |chars|
  requires HasNoDuplicatesUpTo(chars, i)
  requires !Contains(chars[..i], chars[i])
  ensures HasNoDuplicatesUpTo(chars, i + 1)
{
  ContainsPrefixEquiv(chars, chars[i], i);
  assert !(exists k :: 0 <= k < i && chars[k] == chars[i]);
  forall a, b | 0 <= a && a < b && b < i + 1
    ensures chars[a] != chars[b]
  {
    if b < i {
      assert 0 <= a < b < i;
    } else {
      assert b == i;
      assert 0 <= a < i;
      assert chars[a] != chars[i];
    }
  }
}

/* helper modified by LLM (iteration 5): CountChar lower bound with a known index */
lemma CountCharAtLeastOneIfIndex(chars: seq<char>, c: char, k: int)
  requires 0 <= k < |chars| && chars[k] == c
  ensures CountChar(chars, c) >= 1
  decreases k
{
  if k == 0 {
    assert chars[0] == c;
  } else {
    if chars[0] == c {
      // Head contributes 1, so CountChar >= 1 trivially
    } else {
      CountCharAtLeastOneIfIndex(chars[1..], c, k - 1);
    }
  }
}

/* helper modified by LLM (iteration 5): CountChar lower bound with two known indices */
lemma CountCharAtLeastTwoIfTwoIndices(chars: seq<char>, c: char, i: int, j: int)
  requires 0 <= i < j < |chars| && chars[i] == c && chars[j] == c
  ensures CountChar(chars, c) >= 2
  decreases i
{
  if i == 0 {
    assert 0 < |chars|;
    assert chars[0] == c;
    assert 0 <= j - 1 < |chars[1..]|;
    CountCharAtLeastOneIfIndex(chars[1..], c, j - 1);
  } else {
    CountCharAtLeastTwoIfTwoIndices(chars[1..], c, i - 1, j - 1);
  }
}

/* helper modified by LLM (iteration 5): Up-to-full implies global no-duplicates */
lemma UpToFullIsSame(chars: seq<char>)
  ensures HasNoDuplicatesUpTo(chars, |chars|) ==> HasNoDuplicates(chars)
{
  if HasNoDuplicatesUpTo(chars, |chars|) {
    assert forall i: int, j: int :: 0 <= i < j < |chars| ==> chars[i] != chars[j];
    assert HasNoDuplicates(chars);
  }
}

/* helper modified by LLM (iteration 5): From two indices equal to c, the second occurrence predicate holds */
lemma SecondOccurrenceFromTwoIndices(chars: seq<char>, c: char, i: int, j: int)
  requires 0 <= i < j < |chars| && chars[i] == c && chars[j] == c
  ensures SecondOccurrenceExists(chars, c)
{
  assert exists i0, j0 :: 0 <= i0 < j0 < |chars| && chars[i0] == c && chars[j0] == c;
}

/* helper modified by LLM (iteration 5): Package witnesses for the nested existential with no-duplicate prefix */
lemma ExistsFirstSecondWithNoDupPrefix(chars: seq<char>, c: char, firstIdx: int, secondIdx: int)
  requires 0 <= firstIdx < secondIdx < |chars|
  requires chars[firstIdx] == c && chars[secondIdx] == c
  requires HasNoDuplicatesUpTo(chars, secondIdx)
  ensures (exists firstIdx0, secondIdx0 :: 0 <= firstIdx0 < secondIdx0 < |chars| && chars[firstIdx0] == c && chars[secondIdx0] == c && HasNoDuplicatesUpTo(chars, secondIdx0))
{
  assert exists firstIdx0, secondIdx0 :: 0 <= firstIdx0 < secondIdx0 < |chars| && chars[firstIdx0] == c && chars[secondIdx0] == c && HasNoDuplicatesUpTo(chars, secondIdx0);
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
  /* code modified by LLM (iteration 5): Linear scan to find first repeated char; maintain no-dup prefix and construct witnesses */
  var chars := s[..];
  var n := |chars|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant HasNoDuplicatesUpTo(chars, i)
  {
    var c := chars[i];
    if Contains(chars[..i], c) {
      // Satisfy precondition for FirstOccurrenceIndex on prefix
      ContainsPrefixEquiv(chars, c, i);
      var firstIdx := FirstOccurrenceIndex(chars[..i], c);
      assert 0 <= firstIdx < i;
      assert chars[..i][firstIdx] == c;
      assert chars[firstIdx] == c;
      assert i < |chars| && chars[i] == c;

      // Establish required postconditions for Some(c)
      CountCharAtLeastTwoIfTwoIndices(chars, c, firstIdx, i);
      SecondOccurrenceFromTwoIndices(chars, c, firstIdx, i);
      assert HasNoDuplicatesUpTo(chars, i);
      ExistsFirstSecondWithNoDupPrefix(chars, c, firstIdx, i);

      result := Some(c);
      return;
    } else {
      // Extend no-dup invariant when current char not in prefix
      ExtendNoDuplicates(chars, i);
      i := i + 1;
    }
  }
  // No repetitions found
  assert HasNoDuplicatesUpTo(chars, |chars|);
  UpToFullIsSame(chars);
  result := None;
}
// </vc-code>
