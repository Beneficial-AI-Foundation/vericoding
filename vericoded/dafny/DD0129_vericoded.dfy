predicate positive(s:seq<int>)
{
  forall u::0<=u<|s| ==> s[u]>=0
  }

predicate isEven(i:int)
requires i>=0
{
  i%2==0
}

function CountEven(s:seq<int>):int
decreases s
requires positive(s)
{
  if s==[] then 0
  else (if (s[|s|-1]%2==0) then 1 else 0)+CountEven(s[..|s|-1])

}

// <vc-helpers>
lemma CountEvenStep(s: seq<int>, i: int)
  requires positive(s)
  requires 0 <= i < |s|
  ensures CountEven(s[..i+1]) == CountEven(s[..i]) + (if s[i] % 2 == 0 then 1 else 0)
{
  assert s[..i+1] == s[..i] + [s[i]];
  
  var prefix := s[..i];
  var extended := s[..i+1];
  
  // Prove by induction on the definition of CountEven
  if i == 0 {
    assert prefix == [];
    assert extended == [s[0]];
    assert CountEven(prefix) == 0;
    assert CountEven(extended) == (if s[0] % 2 == 0 then 1 else 0);
  } else {
    assert extended[..|extended|-1] == prefix;
    assert extended[|extended|-1] == s[i];
    assert CountEven(extended) == (if extended[|extended|-1] % 2 == 0 then 1 else 0) + CountEven(extended[..|extended|-1]);
    assert CountEven(extended) == (if s[i] % 2 == 0 then 1 else 0) + CountEven(prefix);
  }
}
// </vc-helpers>

// <vc-spec>
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
    var old_n := n;
    if v[i] % 2 == 0 {
      n := n + 1;
    }
    
    CountEvenStep(v[..], i);
    assert v[..i+1] == v[..i] + [v[i]];
    assert CountEven(v[..i+1]) == CountEven(v[..i]) + (if v[i] % 2 == 0 then 1 else 0);
    assert n == old_n + (if v[i] % 2 == 0 then 1 else 0);
    assert n == CountEven(v[..i+1]);
    
    i := i + 1;
  }
  
  assert i == v.Length;
  assert v[..i] == v[..];
}
// </vc-code>

