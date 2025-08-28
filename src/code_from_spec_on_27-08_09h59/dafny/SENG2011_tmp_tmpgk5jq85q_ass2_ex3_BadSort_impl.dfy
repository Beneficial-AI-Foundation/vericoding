// verifies
// all bs are before all as which are before all ds

predicate sortedbad(s:string) 
{
    // all b's are before all a's and d's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j &&
    // all a's are after all b's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b' ==> i > j &&
    // all a's are before all d's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j &&
    // all d's are after a;; b's and a's
    forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j
}

// <vc-helpers>
lemma BadSortCorrectness(s: string)
  requires forall k :: 0 <= k < |s| ==> s[k] == 'b' || s[k] == 'a' || s[k] == 'd'
  requires CountChars(s, 'b') >= 0 && CountChars(s, 'a') >= 0 && CountChars(s, 'd') >= 0
  ensures sortedbad(Repeat('b', CountChars(s, 'b')) + Repeat('a', CountChars(s, 'a')) + Repeat('d', CountChars(s, 'd')))
{
  var result := Repeat('b', CountChars(s, 'b')) + Repeat('a', CountChars(s, 'a')) + Repeat('d', CountChars(s, 'd'));
  var nb := CountChars(s, 'b');
  var na := CountChars(s, 'a');
  var nd := CountChars(s, 'd');
  
  RepeatProperties('b', nb);
  RepeatProperties('a', na);
  RepeatProperties('d', nd);
  
  assert forall i :: 0 <= i < nb ==> result[i] == 'b';
  assert forall i :: nb <= i < nb + na ==> result[i] == 'a';
  assert forall i :: nb + na <= i < nb + na + nd ==> result[i] == 'd';
  
  SortedBadLemma(result, nb, na, nd);
}

lemma SortedBadLemma(s: string, nb: nat, na: nat, nd: nat)
  requires |s| == nb + na + nd
  requires forall i :: 0 <= i < nb ==> s[i] == 'b'
  requires forall i :: nb <= i < nb + na ==> s[i] == 'a'
  requires forall i :: nb + na <= i < nb + na + nd ==> s[i] == 'd'
  ensures sortedbad(s)
{
  assert forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'b' && (s[j] == 'a' || s[j] == 'd') ==> i < j;
  assert forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'b' ==> i > j;
  assert forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'a' && s[j] == 'd' ==> i < j;
  assert forall i,j :: 0 <= i < |s| && 0 <= j < |s| && s[i] == 'd' && (s[j] == 'a' || s[j] == 'b') ==> i > j;
}

function CountChars(s: string, c: char): nat
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + CountChars(s[1..], c)
}

function Repeat(c: char, n: nat): string
{
  if n == 0 then ""
  else [c] + Repeat(c, n - 1)
}

lemma MultisetPreservation(s: string)
  requires forall k :: 0 <= k < |s| ==> s[k] == 'b' || s[k] == 'a' || s[k] == 'd'
  ensures multiset(s[..]) == multiset((Repeat('b', CountChars(s, 'b')) + Repeat('a', CountChars(s, 'a')) + Repeat('d', CountChars(s, 'd')))[..])
{
  var result := Repeat('b', CountChars(s, 'b')) + Repeat('a', CountChars(s, 'a')) + Repeat('d', CountChars(s, 'd'));
  CountCharsTotal(s);
  RepeatCountChars('b', CountChars(s, 'b'));
  RepeatCountChars('a', CountChars(s, 'a'));
  RepeatCountChars('d', CountChars(s, 'd'));
  ConcatenationCountChars(Repeat('b', CountChars(s, 'b')), Repeat('a', CountChars(s, 'a')), Repeat('d', CountChars(s, 'd')));
  MultisetCountEquality(s, result);
}

lemma ConcatenationCountChars(s1: string, s2: string, s3: string)
  ensures CountChars(s1 + s2 + s3, 'b') == CountChars(s1, 'b') + CountChars(s2, 'b') + CountChars(s3, 'b')
  ensures CountChars(s1 + s2 + s3, 'a') == CountChars(s1, 'a') + CountChars(s2, 'a') + CountChars(s3, 'a')
  ensures CountChars(s1 + s2 + s3, 'd') == CountChars(s1, 'd') + CountChars(s2, 'd') + CountChars(s3, 'd')
{
  ConcatenationCountCharsHelper(s1, s2 + s3, 'b');
  ConcatenationCountCharsHelper(s1, s2 + s3, 'a');
  ConcatenationCountCharsHelper(s1, s2 + s3, 'd');
  ConcatenationCountCharsHelper(s2, s3, 'b');
  ConcatenationCountCharsHelper(s2, s3, 'a');
  ConcatenationCountCharsHelper(s2, s3, 'd');
}

lemma ConcatenationCountCharsHelper(s1: string, s2: string, c: char)
  ensures CountChars(s1 + s2, c) == CountChars(s1, c) + CountChars(s2, c)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
    ConcatenationCountCharsHelper(s1[1..], s2, c);
  }
}

lemma MultisetCountEquality(s1: string, s2: string)
  requires CountChars(s1, 'b') == CountChars(s2, 'b')
  requires CountChars(s1, 'a') == CountChars(s2, 'a') 
  requires CountChars(s1, 'd') == CountChars(s2, 'd')
  requires forall k :: 0 <= k < |s1| ==> s1[k] == 'b' || s1[k] == 'a' || s1[k] == 'd'
  requires forall k :: 0 <= k < |s2| ==> s2[k] == 'b' || s2[k] == 'a' || s2[k] == 'd'
  requires |s1| == CountChars(s1, 'b') + CountChars(s1, 'a') + CountChars(s1, 'd')
  requires |s2| == CountChars(s2, 'b') + CountChars(s2, 'a') + CountChars(s2, 'd')
  ensures multiset(s1[..]) == multiset(s2[..])
{
  assert |s1| == |s2|;
  MultisetEqualityByCharCount(s1, s2);
}

lemma MultisetEqualityByCharCount(s1: string, s2: string)
  requires |s1| == |s2|
  requires forall k :: 0 <= k < |s1| ==> s1[k] == 'b' || s1[k] == 'a' || s1[k] == 'd'
  requires forall k :: 0 <= k < |s2| ==> s2[k] == 'b' || s2[k] == 'a' || s2[k] == 'd'
  requires CountChars(s1, 'b') == CountChars(s2, 'b')
  requires CountChars(s1, 'a') == CountChars(s2, 'a')
  requires CountChars(s1, 'd') == CountChars(s2, 'd')
  ensures multiset(s1[..]) == multiset(s2[..])
{
  if |s1| == 0 {
    assert s1 == s2 == "";
  } else {
    var c1 := s1[0];
    assert c1 == 'b' || c1 == 'a' || c1 == 'd';
    MultisetEqualityByCharCountHelper(s1, s2, c1);
  }
}

lemma MultisetEqualityByCharCountHelper(s1: string, s2: string, c: char)
  requires |s1| > 0 && s1[0] == c
  requires c == 'b' || c == 'a' || c == 'd'
  requires forall k :: 0 <= k < |s1| ==> s1[k] == 'b' || s1[k] == 'a' || s1[k] == 'd'
  requires forall k :: 0 <= k < |s2| ==> s2[k] == 'b' || s2[k] == 'a' || s2[k] == 'd'
  requires CountChars(s1, 'b') == CountChars(s2, 'b')
  requires CountChars(s1, 'a') == CountChars(s2, 'a')
  requires CountChars(s1, 'd') == CountChars(s2, 'd')
  requires |s1| == |s2|
  ensures multiset(s1[..]) == multiset(s2[..])
{
  assert CountChars(s2, c) > 0;
  var i :| 0 <= i < |s2| && s2[i] == c;
  var s2' := s2[..i] + s2[i+1..];
  assert multiset(s2[..]) == multiset([c]) + multiset(s2'[..]);
  assert multiset(s1[..]) == multiset([c]) + multiset(s1[1..][..]);
  
  assert CountChars(s1[1..], 'b') == CountChars(s2', 'b');
  assert CountChars(s1[1..], 'a') == CountChars(s2', 'a');
  assert CountChars(s1[1..], 'd') == CountChars(s2', 'd');
  
  if |s1[1..]| > 0 {
    MultisetEqualityByCharCount(s1[1..], s2');
  }
}

lemma RepeatProperties(c: char, n: nat)
  ensures |Repeat(c, n)| == n
  ensures forall i :: 0 <= i < n ==> Repeat(c, n)[i] == c
{
  if n == 0 {
    assert Repeat(c, n) == "";
  } else {
    RepeatProperties(c, n - 1);
    assert Repeat(c, n) == [c] + Repeat(c, n - 1);
  }
}

lemma CountCharsCorrect(s: string, c: char)
  ensures CountChars(s, c) <= |s|
  ensures CountChars(s, c) >= 0
{
  if |s| == 0 {
  } else {
    CountCharsCorrect(s[1..], c);
  }
}

lemma CountCharsTotal(s: string)
  requires forall k :: 0 <= k < |s| ==> s[k] == 'b' || s[k] == 'a' || s[k] == 'd'
  ensures |s| == CountChars(s, 'b') + CountChars(s, 'a') + CountChars(s, 'd')
{
  if |s| == 0 {
  } else {
    CountCharsTotal(s[1..]);
  }
}

lemma RepeatCountChars(c: char, n: nat)
  ensures CountChars(Repeat(c, n), c) == n
  ensures c != 'b' ==> CountChars(Repeat(c, n), 'b') == 0
  ensures c != 'a' ==> CountChars(Repeat(c, n), 'a') == 0
  ensures c != 'd' ==> CountChars(Repeat(c, n), 'd') == 0
{
  if n == 0 {
  } else {
    RepeatCountChars(c, n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BadSort(a: string) returns (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd';
ensures sortedbad(b);
ensures multiset(a[..]) == multiset(b[..]);
ensures |a| == |b|;
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var nb := CountChars(a, 'b');
  var na := CountChars(a, 'a');
  var nd := CountChars(a, 'd');
  
  b := Repeat('b', nb) + Repeat('a', na) + Repeat('d', nd);
  
  BadSortCorrectness(a);
  MultisetPreservation(a);
  CountCharsTotal(a);
}
// </vc-code>
