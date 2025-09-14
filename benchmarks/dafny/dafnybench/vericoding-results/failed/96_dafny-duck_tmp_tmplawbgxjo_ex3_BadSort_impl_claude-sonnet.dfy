// program verifies

predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

// <vc-helpers>
lemma MultisetPreservation(s: string, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]][..]) == multiset(s[..])
{
  var s1 := s[i := s[j]];
  var s2 := s1[j := s[i]];
  
  if i == j {
    assert s2 == s;
  } else {
    assert multiset(s2[..]) == multiset(s[..]);
  }
}

lemma SortedBadCharacterOrder(s: string)
  requires sortedbad(s)
  requires forall i :: 0 <= i < |s| ==> s[i] in {'a', 'b', 'd'}
  ensures forall i, j :: 0 <= i < j < |s| && s[i] == 'b' ==> s[j] != 'a' && s[j] != 'd'
  ensures forall i, j :: 0 <= i < j < |s| && s[i] == 'a' ==> s[j] != 'b'
  ensures forall i, j :: 0 <= i < j < |s| && s[j] == 'd' ==> s[i] != 'a' && s[i] != 'b'
{
  forall i, j | 0 <= i < j < |s| && s[i] == 'b'
    ensures s[j] != 'a' && s[j] != 'd'
  {
    if s[j] == 'a' {
      assert s[i] == 'b' && s[j] != 'b';
      assert 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b';
      assert sortedbad(s);
      assert i < j;
      assert false;
    }
    if s[j] == 'd' {
      assert s[i] == 'b' && s[j] != 'b';
      assert 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b';
      assert sortedbad(s);
      assert i < j;
      assert false;
    }
  }
  
  forall i, j | 0 <= i < j < |s| && s[i] == 'a'
    ensures s[j] != 'b'
  {
    if s[j] == 'b' {
      assert s[i] != 'd' && s[j] == 'd';
      assert 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd';
      assert sortedbad(s);
      assert i < j;
      assert false;
    }
  }
  
  forall i, j | 0 <= i < j < |s| && s[j] == 'd'
    ensures s[i] != 'a' && s[i] != 'b'
  {
    if s[i] == 'a' || s[i] == 'b' {
      assert s[i] != 'd' && s[j] == 'd';
      assert 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd';
      assert sortedbad(s);
      assert i < j;
      assert false;
    }
  }
}

predicate IsSorted(s: string, start: int)
  requires 0 <= start <= |s|
{
  sortedbad(s[start..])
}

lemma SortedImpliesOrder(s: string)
  requires sortedbad(s)
  requires forall i :: 0 <= i < |s| ==> s[i] in {'a', 'b', 'd'}
  ensures forall i, j :: 0 <= i < j < |s| && s[i] == 'b' ==> s[j] != 'a' && s[j] != 'd'
  ensures forall i, j :: 0 <= i < j < |s| && s[i] == 'a' ==> s[j] != 'b'
  ensures forall i, j :: 0 <= i < j < |s| && s[j] == 'd' ==> s[i] != 'a' && s[i] != 'b'
{
  SortedBadCharacterOrder(s);
}

lemma CountCardinality(a: string, i: int, c: char)
  requires 0 <= i <= |a|
  ensures |set j | 0 <= j < i && a[j] == c| <= i
{
}

lemma MultisetCountProperty(a: string, aCount: int, bCount: int, dCount: int)
  requires forall i :: 0 <= i < |a| ==> a[i] in {'a', 'b', 'd'}
  requires aCount == |set j | 0 <= j < |a| && a[j] == 'a'|
  requires bCount == |set j | 0 <= j < |a| && a[j] == 'b'|
  requires dCount == |set j | 0 <= j < |a| && a[j] == 'd'|
  ensures multiset(seq(aCount, _ => 'a') + seq(bCount, _ => 'b') + seq(dCount, _ => 'd')) == multiset(a[..])
{
  var aPart := seq(aCount, _ => 'a');
  var bPart := seq(bCount, _ => 'b');
  var dPart := seq(dCount, _ => 'd');
  var result := aPart + bPart + dPart;
  
  var msA := multiset(a[..]);
  var msResult := multiset(result);
  
  assert msA['a'] == |set j | 0 <= j < |a| && a[j] == 'a'| == aCount;
  assert msA['b'] == |set j | 0 <= j < |a| && a[j] == 'b'| == bCount;
  assert msA['d'] == |set j | 0 <= j < |a| && a[j] == 'd'| == dCount;
  
  assert msResult['a'] == aCount;
  assert msResult['b'] == bCount;
  assert msResult['d'] == dCount;
  
  forall x | x !in {'a', 'b', 'd'}
    ensures msA[x] == 0 && msResult[x] == 0
  {
  }
}
// </vc-helpers>

// <vc-spec>
method BadSort(a: string) returns (b: string)
requires forall i :: 0<=i<|a| ==> a[i] in {'b', 'a', 'd'}
ensures sortedbad(b)
ensures multiset(b[..]) == multiset(a[..])
// </vc-spec>
// <vc-code>
{
  var aCount := 0;
  var bCount := 0;
  var dCount := 0;
  
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant aCount + bCount + dCount == i
    invariant aCount <= |multiset(a[..i])['a']|
    invariant bCount <= |multiset(a[..i])['b']|
    invariant dCount <= |multiset(a[..i])['d']|
    invariant forall j :: 0 <= j < i ==> a[j] in {'a', 'b', 'd'}
    invariant forall j :: 0 <= j < i && a[j] == 'a' ==> aCount >= 1
    invariant forall j :: 0 <= j < i && a[j] == 'b' ==> bCount >= 1
    invariant forall j :: 0 <= j < i && a[j] == 'd' ==> dCount >= 1
  {
    CountCardinality(a, i, a[i]);
    if a[i] == 'a' {
      aCount := aCount + 1;
    } else if a[i] == 'b' {
      bCount := bCount + 1;
    } else {
      dCount := dCount + 1;
    }
    i := i + 1;
  }
  
  b := seq(aCount, _ => 'a') + seq(bCount, _ => 'b') + seq(dCount, _ => 'd');
  
  MultisetCountProperty(a, aCount, bCount, dCount);
  
  assert forall i, j :: 0 <= i < j < |b| ==> 
    (b[i] == 'a' ==> b[j] in {'a', 'b', 'd'}) &&
    (b[i] == 'b' ==> b[j] in {'b', 'd'}) &&
    (b[i] == 'd' ==> b[j] == 'd');
    
  SortedImpliesOrder(b);
}
// </vc-code>

