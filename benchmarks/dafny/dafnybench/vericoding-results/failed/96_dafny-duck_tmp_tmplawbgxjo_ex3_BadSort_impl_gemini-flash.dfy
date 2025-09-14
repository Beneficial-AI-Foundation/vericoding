// program verifies

predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

// <vc-helpers>
function countChar(s: seq<char>, c: char): nat
{
  if s == "" then 0 else (if s[0] == c then 1 else 0) + countChar(s[1..], c)
}

lemma lemma_countChar_append(s1: seq<char>, s2: seq<char>, c: char)
  ensures countChar(s1 + s2, c) == countChar(s1, c) + countChar(s2, c)
{
  if s1 == "" {
    calc {
      countChar("", c) + countChar(s2, c);
      0 + countChar(s2, c);
      countChar(s2, c);
      countChar("" + s2, c);
    }
  } else {
    calc {
      countChar(s1 + s2, c);
      (if s1[0] == c then 1 else 0) + countChar(s1[1..] + s2, c);
      { lemma_countChar_append(s1[1..], s2, c); }
      (if s1[0] == c then 1 else 0) + countChar(s1[1..], c) + countChar(s2, c);
      countChar(s1, c) + countChar(s2, c);
    }
  }
}

lemma lemma_countChar_empty_multiset(s: seq<char>, c: char)
  ensures multiset(s)[c] == countChar(s, c)
{
  if s == "" {
    assert multiset(s)[c] == multiset("")[c] == 0;
    assert countChar(s, c) == 0;
  } else {
    lemma_countChar_empty_multiset(s[1..], c);
    if s[0] == c {
      calc {
        multiset(s)[c];
        multiset({s[0]})[c] + multiset(s[1..])[c];
        1 + multiset(s[1..])[c];
        1 + countChar(s[1..], c);
        countChar(s, c);
      }
    } else {
      calc {
        multiset(s)[c];
        multiset({s[0]})[c] + multiset(s[1..])[c];
        0 + multiset(s[1..])[c];
        0 + countChar(s[1..], c);
        countChar(s, c);
      }
    }
  }
}

lemma lemma_multiset_append(s1: seq<char>, s2: seq<char>)
  ensures multiset((s1 + s2)) == multiset(s1) + multiset(s2)
{
  var M := multiset(s1) + multiset(s2);
  var S := multiset((s1 + s2));
  forall c: char | true
    ensures S[c] == M[c]
  {
    lemma_countChar_append(s1, s2, c);
    lemma_countChar_empty_multiset(s1, c);
    lemma_countChar_empty_multiset(s2, c);
    lemma_countChar_empty_multiset(s1 + s2, c);
    assert S[c] == countChar(s1 + s2, c);
    assert M[c] == countChar(s1, c) + countChar(s2, c);
  }
}

lemma lemma_sortedbad_concat(s1: seq<char>, s2: seq<char>, s3: seq<char>)
  requires forall c :: c in {'a', 'b', 'd'}
  requires forall i :: 0 <= i < |s1| ==> s1[i] == 'b'
  requires forall i :: 0 <= i < |s2| ==> s2[i] == 'a'
  requires forall i :: 0 <= i < |s3| ==> s3[i] == 'd'
  ensures sortedbad(s1 + s2 + s3)
{
  var s := s1 + s2 + s3;
  assert forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j
    by {
      if |s1| > 0 {
        assert forall k :: 0 <= k < |s1| ==> s1[k] == 'b';
        assert |s1| == countChar(s1, 'b');
      }
      forall i, j | 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b'
        ensures i < j
      {
        assert i < |s1|; 
        assert s[j] != 'b'; 
        assert j >= |s1|; 
        assert i < j;
      }
    }
  assert forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
    by {
      forall i, j | 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd'
        ensures i < j
      {
        assert j >= |s1| + |s2|; 
        assert s[i] != 'd'; 
        assert i < |s1| + |s2|; 
        assert i < j;
      }
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
  var num_b := 0;
  var num_a := 0;
  var num_d := 0;

  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant num_b == countChar(a[..i], 'b')
    invariant num_a == countChar(a[..i], 'a')
    invariant num_d == countChar(a[..i], 'd')
    invariant forall c :: c !in {'a', 'b', 'd'} ==> countChar(a[..i], c) == 0
  {
    if a[i] == 'b' {
      num_b := num_b + 1;
    } else if a[i] == 'a' {
      num_a := num_a + 1;
    } else if a[i] == 'd' {
      num_d := num_d + 1;
    }
    i := i + 1;
  }

  var s_b := new char[num_b](_ => 'b');
  var s_a := new char[num_a](_ => 'a');
  var s_d := new char[num_d](_ => 'd');

  b := (s_b[..] + s_a[..]) + s_d[..];

  lemma_countChar_empty_multiset(a[..], 'b');
  lemma_countChar_empty_multiset(a[..], 'a');
  lemma_countChar_empty_multiset(a[..], 'd');
  
  assert num_b == multiset(a[..])['b'];
  assert num_a == multiset(a[..])['a'];
  assert num_d == multiset(a[..])['d'];

  lemma_countChar_empty_multiset(s_b[..], 'b');
  lemma_countChar_empty_multiset(s_a[..], 'a');
  lemma_countChar_empty_multiset(s_d[..], 'd');

  assert multiset(s_b[..])['b'] == num_b;
  assert multiset(s_b[..])['a'] == 0;
  assert multiset(s_b[..])['d'] == 0;

  assert multiset(s_a[..])['b'] == 0;
  assert multiset(s_a[..])['a'] == num_a;
  assert multiset(s_a[..])['d'] == 0;

  assert multiset(s_d[..])['b'] == 0;
  assert multiset(s_d[..])['a'] == 0;
  assert multiset(s_d[..])['d'] == num_d;

  lemma_multiset_append(s_b[..], s_a[..]);
  lemma_multiset_append(s_b[..] + s_a[..], s_d[..]);

  assert multiset(b) == multiset(s_b[..]) + multiset(s_a[..]) + multiset(s_d[..]);

  assert multiset(b)['b'] == num_b + 0 + 0 == num_b;
  assert multiset(b)['a'] == 0 + num_a + 0 == num_a;
  assert multiset(b)['d'] == 0 + 0 + num_d == num_d;
  
  forall c | c !in {'a', 'b', 'd'}
    ensures multiset(b)[c] == multiset(a)[c]
  {
    assert multiset(b)[c] == 0;
    assert multiset(a)[c] == 0;
  }

  assert multiset(b) == multiset(a);

  lemma_sortedbad_concat(s_b[..], s_a[..], s_d[..]);
}
// </vc-code>

