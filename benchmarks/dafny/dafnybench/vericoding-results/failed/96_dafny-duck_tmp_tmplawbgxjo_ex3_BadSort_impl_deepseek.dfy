// program verifies

predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

// <vc-helpers>
lemma CountLemma(s: string, c: char)
  requires forall i :: 0<=i<|s| ==> s[i] in {'b', 'a', 'd'}
  ensures count(s, 'a') + count(s, 'b') + count(s, 'd') == |s|
{
}

function count(s: string, c: char): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + count(s[1..], c)
}

lemma MultisetCountLemma(s: string, t: string)
  ensures multiset(s[..]) == multiset(t[..]) <==> 
          count(s, 'a') == count(t, 'a') && 
          count(s, 'b') == count(t, 'b') && 
          count(s, 'd') == count(t, 'd')
{
}

lemma SortedBadImpliesStructure(s: string)
  requires sortedbad(s)
  requires forall i :: 0<=i<|s| ==> s[i] in {'b', 'a', 'd'}
  ensures exists na, nb, nd :: 
    na == count(s, 'a') && nb == count(s, 'b') && nd == count(s, 'd') &&
    s == SeqConcat(SeqConcat(SeqRepeat('b', nb), SeqRepeat('a', na)), SeqRepeat('d', nd))
{
}

function SeqRepeat(c: char, n: nat): seq<char>
  decreases n
{
  if n == 0 then []
  else [c] + SeqRepeat(c, n-1)
}

function SeqConcat(s1: seq<char>, s2: seq<char>): seq<char>
{
  s1 + s2
}

lemma SeqRepeatProperties(c: char, n: nat)
  ensures |SeqRepeat(c, n)| == n
  ensures forall i :: 0 <= i < |SeqRepeat(c, n)| ==> SeqRepeat(c, n)[i] == c
{
}

lemma SeqConcatProperties(s1: seq<char>, s2: seq<char>)
  ensures |SeqConcat(s1, s2)| == |s1| + |s2|
  ensures forall i :: 0 <= i < |s1| ==> SeqConcat(s1, s2)[i] == s1[i]
  ensures forall i :: |s1| <= i < |s1| + |s2| ==> SeqConcat(s1, s2)[i] == s2[i - |s1|]
{
}

lemma SortedbadCheck(s: string, nb: nat, na: nat, nd: nat)
  requires s == SeqConcat(SeqConcat(SeqRepeat('b', nb), SeqRepeat('a', na)), SeqRepeat('d', nd))
  ensures sortedbad(s)
{
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
  var na := count(a, 'a');
  var nb := count(a, 'b');
  var nd := count(a, 'd');
  CountLemma(a, 'a');
  
  var s1 := SeqRepeat('b', nb);
  var s2 := SeqRepeat('a', na);
  var s3 := SeqRepeat('d', nd);
  
  var bs := SeqConcat(s1, s2);
  b := SeqConcat(bs, s3);
  
  assert count(b, 'a') == count(a, 'a');
  assert count(b, 'b') == count(a, 'b');
  assert count(b, 'd') == count(a, 'd');
  MultisetCountLemma(a, b);
  
  SortedbadCheck(b, nb, na, nd);
}
// </vc-code>

