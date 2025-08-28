// program verifies

predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

// <vc-helpers>
lemma SortedBadProperties(s: string)
  requires sortedbad(s)
  ensures forall i, j :: 0 <= i < j < |s| && s[i] == 'b' ==> s[j] != 'b'
  ensures forall i, j :: 0 <= i < j < |s| && s[j] == 'd' ==> s[i] != 'd'
{
  forall i, j | 0 <= i < j < |s| && s[i] == 'b'
    ensures s[j] != 'b'
  {
    if s[j] != 'b' {
    } else {
      assert s[i] == 'b' && s[j] == 'b';
      assert i <= j;
      assert s[i] == 'b' && s[j] != 'b' ==> i < j;
    }
  }
  
  forall i, j | 0 <= i < j < |s| && s[j] == 'd'
    ensures s[i] != 'd'
  {
    if s[i] != 'd' {
    } else {
      assert s[i] == 'd' && s[j] == 'd';
      assert i <= j;
      assert s[i] != 'd' && s[j] == 'd' ==> i < j;
    }
  }
}

lemma ConcatPreservesSortedBad(s1: string, s2: string)
  requires sortedbad(s1)
  requires sortedbad(s2)
  requires forall i :: 0 <= i < |s1| ==> s1[i] != 'b'
  requires forall i :: 0 <= i < |s2| ==> s2[i] != 'd'
  ensures sortedbad(s1 + s2)
{
}

lemma SingleCharSortedBad(c: char)
  ensures sortedbad([c])
{
}

lemma EmptySortedBad()
  ensures sortedbad("")
{
}

lemma AllSameCharSortedBad(s: string, c: char)
  requires forall i :: 0 <= i < |s| ==> s[i] == c
  ensures sortedbad(s)
{
}

lemma MultisetConcatenation(s1: string, s2: string)
  ensures multiset((s1 + s2)[..]) == multiset(s1[..]) + multiset(s2[..])
{
}

lemma MultisetSingleChar(c: char)
  ensures multiset([c][..]) == multiset{c}
{
}

lemma MultisetPreservationLoop(nonB: string, bChars: string, dChars: string, newChar: char, a: string, i: int)
  requires 0 <= i < |a|
  requires multiset(nonB[..]) + multiset(bChars[..]) + multiset(dChars[..]) == multiset(a[..i])
  ensures newChar == a[i] ==> multiset((nonB + [newChar])[..]) + multiset(bChars[..]) + multiset(dChars[..]) == multiset(a[..i+1])
  ensures newChar == a[i] ==> multiset(nonB[..]) + multiset((bChars + [newChar])[..]) + multiset(dChars[..]) == multiset(a[..i+1])
  ensures newChar == a[i] ==> multiset(nonB[..]) + multiset(bChars[..]) + multiset((dChars + [newChar])[..]) == multiset(a[..i+1])
{
  if newChar == a[i] {
    calc {
      multiset((nonB + [newChar])[..]) + multiset(bChars[..]) + multiset(dChars[..]);
      == multiset(nonB[..]) + multiset([newChar][..]) + multiset(bChars[..]) + multiset(dChars[..]);
      == multiset(nonB[..]) + multiset(bChars[..]) + multiset(dChars[..]) + multiset{newChar};
      == multiset(a[..i]) + multiset{a[i]};
      == { assert a[..i+1] == a[..i] + [a[i]]; }
      multiset(a[..i+1]);
    }
  }
}

lemma ConcatPreservesMultiset(s1: string, s2: string, s3: string)
  ensures multiset((s1 + s2 + s3)[..]) == multiset(s1[..]) + multiset(s2[..]) + multiset(s3[..])
{
  MultisetConcatenation(s1, s2 + s3);
  MultisetConcatenation(s2, s3);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BadSort(a: string) returns (b: string)
requires forall i :: 0<=i<|a| ==> a[i] in {'b', 'a', 'd'}
ensures sortedbad(b)
ensures multiset(b[..]) == multiset(a[..])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var nonB := "";
  var bChars := "";
  var dChars := "";
  
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant multiset(nonB[..]) + multiset(bChars[..]) + multiset(dChars[..]) == multiset(a[..i])
    invariant forall j :: 0 <= j < |nonB| ==> nonB[j] == 'a'
    invariant forall j :: 0 <= j < |bChars| ==> bChars[j] == 'b'
    invariant forall j :: 0 <= j < |dChars| ==> dChars[j] == 'd'
  {
    if a[i] == 'a' {
      MultisetPreservationLoop(nonB, bChars, dChars, a[i], a, i);
      nonB := nonB + [a[i]];
    } else if a[i] == 'b' {
      MultisetPreservationLoop(nonB, bChars, dChars, a[i], a, i);
      bChars := bChars + [a[i]];
    } else {
      MultisetPreservationLoop(nonB, bChars, dChars, a[i], a, i);
      dChars := dChars + [a[i]];
    }
    i := i + 1;
  }
  
  b := nonB + bChars + dChars;
  
  ConcatPreservesMultiset(nonB, bChars, dChars);
  
  AllSameCharSortedBad(nonB, 'a');
  AllSameCharSortedBad(bChars, 'b');
  AllSameCharSortedBad(dChars, 'd');
  
  ConcatPreservesSortedBad(nonB, bChars + dChars);
}
// </vc-code>
