// program verifies

predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

// <vc-helpers>
lemma SortedBadProperty(s: string)
  ensures sortedbad(s) <==> (forall i, j :: 0 <= i < j < |s| ==> 
    (s[i] == 'b' ==> s[j] == 'b') && 
    (s[j] == 'd' ==> s[i] == 'd'))
{
  if sortedbad(s) {
    forall i, j | 0 <= i < j < |s|
      ensures (s[i] == 'b' ==> s[j] == 'b') && (s[j] == 'd' ==> s[i] == 'd')
    {
      if s[i] == 'b' && s[j] != 'b' {
        assert s[i] == 'b' && s[j] != 'b' && 0 <= i <= j < |s|;
        assert false;
      }
      if s[i] != 'd' && s[j] == 'd' {
        assert s[i] != 'd' && s[j] == 'd' && 0 <= i <= j < |s|;
      }
    }
  }
}

function CountChar(s: string, c: char): nat
{
  if |s| == 0 then 0
  else if s[0] == c then 1 + CountChar(s[1..], c)
  else CountChar(s[1..], c)
}

lemma CountCharMultiset(s: string, c: char)
  ensures CountChar(s, c) == multiset(s[..])[c]
{
  if |s| == 0 {
  } else {
    CountCharMultiset(s[1..], c);
    assert s[..] == [s[0]] + s[1..];
  }
}

function RepeatChar(c: char, n: nat): string
  ensures |RepeatChar(c, n)| == n
  ensures forall i :: 0 <= i < n ==> RepeatChar(c, n)[i] == c
  ensures forall ch :: ch != c ==> multiset(RepeatChar(c, n)[..])[ch] == 0
  ensures multiset(RepeatChar(c, n)[..])[c] == n
{
  if n == 0 then ""
  else [c] + RepeatChar(c, n - 1)
}

lemma RepeatCharMultiset(c: char, n: nat)
  ensures multiset(RepeatChar(c, n)[..]) == multiset(seq(n, i => c))
{
  if n == 0 {
    assert RepeatChar(c, 0) == "";
    assert seq(0, i => c) == [];
  } else {
    RepeatCharMultiset(c, n - 1);
    var s1 := RepeatChar(c, n);
    var s2 := seq(n, i => c);
    assert s1 == [c] + RepeatChar(c, n - 1);
    assert s2 == [c] + seq(n - 1, i => c);
    assert multiset(s1[..]) == multiset([c]) + multiset(RepeatChar(c, n - 1)[..]);
    assert multiset(s2) == multiset([c]) + multiset(seq(n - 1, i => c));
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
  var countB := CountChar(a, 'b');
  var countA := CountChar(a, 'a');
  var countD := CountChar(a, 'd');
  
  b := RepeatChar('b', countB) + RepeatChar('a', countA) + RepeatChar('d', countD);
  
  // Prove that b is sorted according to sortedbad
  assert forall i :: 0 <= i < countB ==> b[i] == 'b';
  assert forall i :: countB <= i < countB + countA ==> b[i] == 'a';
  assert forall i :: countB + countA <= i < |b| ==> b[i] == 'd';
  
  // Prove sortedbad(b)
  assert forall i, j :: 0 <= i <= j < |b| && b[i] == 'b' && b[j] != 'b' ==> i < countB && j >= countB && i < j;
  assert forall i, j :: 0 <= i <= j < |b| && b[i] != 'd' && b[j] == 'd' ==> i < countB + countA && j >= countB + countA && i < j;
  SortedBadProperty(b);
  
  // Prove multiset equality
  CountCharMultiset(a, 'b');
  CountCharMultiset(a, 'a');
  CountCharMultiset(a, 'd');
  
  assert countB + countA + countD == |a| by {
    assert forall c :: c in multiset(a[..]) ==> c in {'b', 'a', 'd'};
    assert multiset(a[..]) == multiset{'b' := countB, 'a' := countA, 'd' := countD};
  }
  
  assert |b| == countB + countA + countD;
  assert |b| == |a|;
  
  RepeatCharMultiset('b', countB);
  RepeatCharMultiset('a', countA);
  RepeatCharMultiset('d', countD);
  
  assert multiset(b[..]) == multiset(RepeatChar('b', countB)[..]) + multiset(RepeatChar('a', countA)[..]) + multiset(RepeatChar('d', countD)[..]);
  assert multiset(b[..])['b'] == countB;
  assert multiset(b[..])['a'] == countA;
  assert multiset(b[..])['d'] == countD;
  
  assert multiset(b[..]) == multiset(a[..]);
}
// </vc-code>

