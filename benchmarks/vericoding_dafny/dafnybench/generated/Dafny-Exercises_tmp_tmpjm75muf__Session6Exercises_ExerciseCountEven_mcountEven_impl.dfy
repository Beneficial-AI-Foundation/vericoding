predicate positive(s:seq<int>)
{
  forall u::0<=u<|s| ==> s[u]>=0
  }

predicate isEven(i:int)
requires i>=0
{
  i%2==0
}

// <vc-spec>
function CountEven(s:seq<int>):int
decreases s
requires positive(s)
{
  if s==[] then 0
  else (if (s[|s|-1]%2==0) then 1 else 0)+CountEven(s[..|s|-1])

}

lemma ArrayFacts<T>()
    ensures forall v : array<T>  :: v[..v.Length] == v[..]
    ensures forall v : array<T>  :: v[0..] == v[..]
    ensures forall v : array<T>  :: v[0..v.Length] == v[..]

    ensures forall v : array<T>  ::|v[0..v.Length]|==v.Length
    ensures forall v : array<T> | v.Length>=1 ::|v[1..v.Length]|==v.Length-1

    ensures forall v : array<T>  ::forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
  {}

// <vc-helpers>
lemma CountEvenSplit(s: seq<int>, k: nat)
  requires positive(s)
  requires k < |s|
  ensures CountEven(s) == CountEven(s[..k+1]) + CountEven(s[k+1..])
  decreases |s| - k
{
  CountEvenAddOne(s, k);
  CountEvenRemoveOne(s, k);
}

lemma CountEvenAddOne(s: seq<int>, k: nat)
  requires positive(s)
  requires k < |s|
  ensures CountEven(s[..k+1]) == CountEven(s[..k]) + (if s[k] % 2 == 0 then 1 else 0)
  decreases k
{
  if k == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
    assert CountEven(s[..0]) == 0;
    if s[0] % 2 == 0 {
      assert CountEven(s[..1]) == 1;
    } else {
      assert CountEven(s[..1]) == 0;
    }
  } else {
    CountEvenAddOne(s, k-1);
    var s_k := s[..k];
    var s_k1 := s[..k+1];
    assert s_k1 == s_k + [s[k]];
    
    // Since CountEven processes from right to left, we need to show the relationship
    if s[k] % 2 == 0 {
      assert CountEven(s_k1) == 1 + CountEven(s_k1[..|s_k1|-1]);
      assert s_k1[..|s_k1|-1] == s_k;
    } else {
      assert CountEven(s_k1) == 0 + CountEven(s_k1[..|s_k1|-1]);
      assert s_k1[..|s_k1|-1] == s_k;
    }
  }
}

lemma CountEvenRemoveOne(s: seq<int>, idx: nat)
  requires positive(s)
  requires idx < |s|
  ensures CountEven(s) == (if s[idx] % 2 == 0 then 1 else 0) + CountEven(s[idx+1..])
  decreases |s| - idx
{
  if |s| == 1 {
    assert s[idx+1..] == [];
    assert CountEven(s[idx+1..]) == 0;
    assert CountEven(s) == (if s[idx] % 2 == 0 then 1 else 0);
  } else {
    var last_idx := |s| - 1;
    if idx == last_idx {
      assert s[idx+1..] == [];
      assert CountEven(s[idx+1..]) == 0;
      assert CountEven(s) == (if s[last_idx] % 2 == 0 then 1 else 0) + CountEven(s[..last_idx]);
      assert s[idx] == s[last_idx];
    } else {
      assert s == s[..last_idx] + [s[last_idx]];
      assert CountEven(s) == (if s[last_idx] % 2 == 0 then 1 else 0) + CountEven(s[..last_idx]);
      CountEvenRemoveOne(s[..last_idx], idx);
      assert CountEven(s[..last_idx]) == (if s[idx] % 2 == 0 then 1 else 0) + CountEven(s[..last_idx][idx+1..]);
      assert s[..last_idx][idx+1..] == s[idx+1..last_idx];
      assert s[idx+1..] == s[idx+1..last_idx] + [s[last_idx]];
      assert CountEven(s[idx+1..]) == (if s[last_idx] % 2 == 0 then 1 else 0) + CountEven(s[idx+1..last_idx]);
    }
  }
}

lemma CountEvenAppend(s1: seq<int>, s2: seq<int>)
  requires positive(s1)
  requires positive(s2)
  requires |s2| == 1
  ensures positive(s1 + s2)
  ensures CountEven(s1 + s2) == CountEven(s1) + CountEven(s2)
{
  var combined := s1 + s2;
  if |s1| == 0 {
    assert combined == s2;
  } else {
    assert combined[|combined|-1] == s2[0];
    assert combined[..|combined|-1] == s1;
    assert CountEven(combined) == (if combined[|combined|-1] % 2 == 0 then 1 else 0) + CountEven(combined[..|combined|-1]);
    assert CountEven(combined) == (if s2[0] % 2 == 0 then 1 else 0) + CountEven(s1);
    assert CountEven(s2) == (if s2[0] % 2 == 0 then 1 else 0);
  }
}
// </vc-helpers>

method mcountEven(v:array<int>) 
returns (n:int)
requires positive(v[..])
ensures  n==CountEven(v[..])
// </vc-spec>
// <vc-code>
{
  n := 0;
  var i := 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant n == CountEven(v[..i])
  {
    if v[i] % 2 == 0 {
      n := n + 1;
    }
    i := i + 1;
    
    // Help prove the invariant
    CountEvenAddOne(v[..], i-1);
  }
  
  ArrayFacts<int>();
}
// </vc-code>