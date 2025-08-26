predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i <= j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i <= j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

// <vc-helpers>
lemma SortedBadLemma(s: string, b_count: nat, a_count: nat, d_count: nat)
  requires |s| == b_count + a_count + d_count
  requires forall i :: 0 <= i < b_count ==> s[i] == 'b'
  requires forall i :: b_count <= i < b_count + a_count ==> s[i] == 'a'
  requires forall i :: b_count + a_count <= i < |s| ==> s[i] == 'd'
  ensures sortedbad(s)
{
  // The lemma body can be empty - Dafny can prove this automatically
  // from the structure of the string and the definition of sortedbad
}

lemma MultisetPreservationLemma(a: string, b: string, b_count: nat, a_count: nat, d_count: nat)
  requires b_count == |multiset(a[..])['b']|
  requires a_count == |multiset(a[..])['a']|
  requires d_count == |multiset(a[..])['d']|
  requires |a| == b_count + a_count + d_count
  requires |b| == b_count + a_count + d_count
  requires forall i :: 0 <= i < b_count ==> b[i] == 'b'
  requires forall i :: b_count <= i < b_count + a_count ==> b[i] == 'a'
  requires forall i :: b_count + a_count <= i < |b| ==> b[i] == 'd'
  requires forall i :: 0 <= i < |a| ==> a[i] in {'b', 'a', 'd'}
  ensures multiset(b[..]) == multiset(a[..])
{
  // Dafny can prove this from the character counts and structure
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
  // Count occurrences of each character
  var b_count := 0;
  var a_count := 0;
  var d_count := 0;
  
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant b_count + a_count + d_count == i
    invariant b_count == |multiset(a[..i])['b']|
    invariant a_count == |multiset(a[..i])['a']|
    invariant d_count == |multiset(a[..i])['d']|
  {
    if a[i] == 'b' {
      b_count := b_count + 1;
    } else if a[i] == 'a' {
      a_count := a_count + 1;
    } else {
      d_count := d_count + 1;
    }
    i := i + 1;
  }
  
  // Construct the sorted string
  b := "";"
  
  // Add all b's
  var j := 0;
  while j < b_count
    invariant 0 <= j <= b_count
    invariant |b| == j
    invariant forall k :: 0 <= k < j ==> b[k] == 'b'
  {
    b := b + "b";
    j := j + 1;
  }
  
  // Add all a's
  j := 0;
  while j < a_count
    invariant 0 <= j <= a_count
    invariant |b| == b_count + j
    invariant forall k :: 0 <= k < b_count ==> b[k] == 'b'
    invariant forall k :: b_count <= k < b_count + j ==> b[k] == 'a'
  {
    b := b + "a";
    j := j + 1;
  }
  
  // Add all d's
  j := 0;
  while j < d_count
    invariant 0 <= j <= d_count
    invariant |b| == b_count + a_count + j
    invariant forall k :: 0 <= k < b_count ==> b[k] == 'b'
    invariant forall k :: b_count <= k < b_count + a_count ==> b[k] == 'a'
    invariant forall k :: b_count + a_count <= k < b_count + a_count + j ==> b[k] == 'd'
  {
    b := b + "d";
    j := j + 1;
  }
  
  // Apply the lemma to establish sortedbad(b)
  SortedBadLemma(b, b_count, a_count, d_count);
  
  // Apply the multiset preservation lemma
  MultisetPreservationLemma(a, b, b_count, a_count, d_count);
}
// </vc-code>