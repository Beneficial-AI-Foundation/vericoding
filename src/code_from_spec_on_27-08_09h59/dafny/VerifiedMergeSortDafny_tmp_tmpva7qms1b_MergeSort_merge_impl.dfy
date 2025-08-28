predicate merged(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, end: int)
  reads b
  requires end - start  == |a2| + |a1|
  requires 0 <= start <= end <= b.Length
{
  multiset(a1) + multiset(a2) == multiset(b[start..end])
}

predicate sorted_slice(a: array<int>, start: int, end: int)
  requires 0 <= start <= end <= a.Length
  reads a
{
  forall i, j :: start <= i <= j < end ==> a[i] <= a[j]
}

predicate sorted_seq(a: seq<int>)
{
  forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

predicate sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// <vc-helpers>
lemma multiset_preservation_step(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, pos: int, i1: int, i2: int)
  requires 0 <= start <= pos < b.Length
  requires 0 <= i1 <= |a1|
  requires 0 <= i2 <= |a2|
  requires pos - start == i1 + i2
  requires multiset(a1[..i1]) + multiset(a2[..i2]) == multiset(b[start..pos])
  ensures i1 < |a1| ==> multiset(a1[..i1+1]) + multiset(a2[..i2]) == multiset(b[start..pos]) + multiset([a1[i1]])
  ensures i2 < |a2| ==> multiset(a1[..i1]) + multiset(a2[..i2+1]) == multiset(b[start..pos]) + multiset([a2[i2]])
{
  if i1 < |a1| {
    assert a1[..i1+1] == a1[..i1] + [a1[i1]];
  }
  if i2 < |a2| {
    assert a2[..i2+1] == a2[..i2] + [a2[i2]];
  }
}

lemma sorted_preservation(b: array<int>, start: int, pos: int, val: int)
  requires 0 <= start <= pos < b.Length
  requires sorted_slice(b, start, pos)
  requires pos == start || b[pos-1] <= val
  ensures b[pos] == val ==> sorted_slice(b, start, pos+1)
{
  if pos > start && b[pos] == val {
    forall i, j | start <= i <= j < pos+1
      ensures b[i] <= b[j]
    {
      if j == pos {
        if i == pos {
          assert b[i] <= b[j];
        } else {
          assert i < pos;
          assert b[i] <= b[pos-1] <= val == b[j];
        }
      } else {
        assert i <= j < pos;
        assert b[i] <= b[j];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  modifies b
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires end - start == |a1| + |a2|
  requires 0 <= start < end < |a1| && end <= |a2| < b.Length
  requires end < |a1| && end < |a2|
  ensures sorted_slice(b, start, end)
  requires b.Length == |a2| + |a1|
  ensures merged(a1, a2, b, start, end)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var i1 := 0;
  var i2 := 0;
  var pos := start;
  
  while i1 < |a1| || i2 < |a2|
    invariant 0 <= i1 <= |a1|
    invariant 0 <= i2 <= |a2|
    invariant pos == start + i1 + i2
    invariant pos <= end
    invariant sorted_slice(b, start, pos)
    invariant multiset(a1[..i1]) + multiset(a2[..i2]) == multiset(b[start..pos])
    invariant i1 < |a1| && i2 < |a2| ==> (pos == start || b[pos-1] <= a1[i1] || b[pos-1] <= a2[i2])
    invariant i1 < |a1| && i2 >= |a2| ==> (pos == start || b[pos-1] <= a1[i1])
    invariant i1 >= |a1| && i2 < |a2| ==> (pos == start || b[pos-1] <= a2[i2])
  {
    multiset_preservation_step(a1, a2, b, start, pos, i1, i2);
    
    if i1 >= |a1| {
      b[pos] := a2[i2];
      sorted_preservation(b, start, pos, a2[i2]);
      i2 := i2 + 1;
    } else if i2 >= |a2| {
      b[pos] := a1[i1];
      sorted_preservation(b, start, pos, a1[i1]);
      i1 := i1 + 1;
    } else if a1[i1] <= a2[i2] {
      b[pos] := a1[i1];
      sorted_preservation(b, start, pos, a1[i1]);
      i1 := i1 + 1;
    } else {
      b[pos] := a2[i2];
      sorted_preservation(b, start, pos, a2[i2]);
      i2 := i2 + 1;
    }
    pos := pos + 1;
  }
  
  assert i1 == |a1| && i2 == |a2|;
  assert a1[..i1] == a1 && a2[..i2] == a2;
  assert pos == end;
}
// </vc-code>
