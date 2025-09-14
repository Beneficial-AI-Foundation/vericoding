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
lemma CountLemma(s: string, c: char)
  requires forall k :: 0 <= k < |s| ==> s[k] == 'b' || s[k] == 'a' || s[k] == 'd'
  ensures |s| == count(s, 'b') + count(s, 'a') + count(s, 'd')
{
}

function count(s: string, c: char): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + count(s[1..], c)
}

lemma SortedBadImpliesOrder(s: string)
  requires sortedbad(s)
  ensures forall i :: 0 <= i < |s| ==>
    (s[i] == 'b') ==> (forall j :: i < j < |s| ==> s[j] != 'b')
  ensures forall i :: 0 <= i < |s| ==>
    (s[i] == 'a') ==> (forall j :: 0 <= j < i ==> s[j] != 'd') && (forall j :: i < j < |s| ==> s[j] != 'b' && s[j] != 'a')
{
}

lemma MultisetPreservation(a: string, b: string)
  requires multiset(a[..]) == multiset(b[..])
  ensures forall c :: count(a, c) == count(b, c)
{
}

lemma CountAddChar(s: string, c: char)
  ensures count(s + [c], c) == count(s, c) + 1
  ensures forall d :: d != c ==> count(s + [c], d) == count(s, d)
{
  if |s| > 0 {
    CountAddChar(s[1..], c);
  }
}

lemma MultisetConcat(s1: string, s2: string)
  ensures multiset((s1 + s2)[..]) == multiset(s1[..]) + multiset(s2[..])
{
}

lemma CountTake(s: string, n: nat, c: char)
  requires n <= |s|
  ensures count(s[..n], c) <= count(s, c)
{
}

lemma CountCons(s: string, c: char, d: char)
  ensures count([c] + s, d) == (if c == d then 1 else 0) + count(s, d)
{
}

lemma CountZero(s: string, c: char)
  ensures |s| == 0 ==> count(s, c) == 0
{
}
// </vc-helpers>

// <vc-spec>
method BadSort(a: string) returns (b: string)
requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd';
ensures sortedbad(b);
ensures multiset(a[..]) == multiset(b[..]);
ensures |a| == |b|;
// </vc-spec>
// <vc-code>
{
  var count_b := count(a, 'b');
  var count_a := count(a, 'a');
  var count_d := count(a, 'd');
  
  CountLemma(a, 'b');
  
  var i := 0;
  b := "";
  
  while i < count_b
    invariant |b| == i
    invariant forall k :: 0 <= k < i ==> b[k] == 'b'
    invariant count(b, 'b') == i
    invariant count(b, 'a') == 0
    invariant count(b, 'd') == 0
    invariant multiset(b[..]) == multiset((new string [c | k in 0..i :: 'b'])[..])
    decreases count_b - i
  {
    b := b + ['b'];
    i := i + 1;
  }
  
  i := 0;
  while i < count_a
    invariant |b| == count_b + i
    invariant forall k :: 0 <= k < count_b ==> b[k] == 'b'
    invariant forall k :: count_b <= k < count_b + i ==> b[k] == 'a'
    invariant count(b, 'b') == count_b
    invariant count(b, 'a') == i
    invariant count(b, 'd') == 0
    invariant multiset(b[..]) == multiset(a[0..count_b + i])
    decreases count_a - i
  {
    b := b + ['a'];
    i := i + 1;
  }
  
  i := 0;
  while i < count_d
    invariant |b| == count_b + count_a + i
    invariant forall k :: 0 <= k < count_b ==> b[k] == 'b'
    invariant forall k :: count_b <= k < count_b + count_a ==> b[k] == 'a'
    invariant forall k :: count_b + count_a <= k < count_b + count_a + i ==> b[k] == 'd'
    invariant count(b, 'b') == count_b
    invariant count(b, 'a') == count_a
    invariant count(b, 'd') == i
    invariant multiset(b[..]) == multiset(a[..])
    decreases count_d - i
  {
    b := b + ['d'];
    i := i + 1;
  }
}
// </vc-code>

