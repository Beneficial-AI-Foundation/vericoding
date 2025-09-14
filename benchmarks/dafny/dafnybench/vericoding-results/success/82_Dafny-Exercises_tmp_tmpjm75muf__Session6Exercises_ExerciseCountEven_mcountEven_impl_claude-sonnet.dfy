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
lemma CountEvenPrefix(s: seq<int>, i: int)
requires positive(s)
requires 0 <= i <= |s|
ensures CountEven(s[..i]) == CountEven(s[0..i])
{
}

lemma CountEvenIncremental(s: seq<int>, i: int)
requires positive(s)
requires 0 <= i < |s|
ensures CountEven(s[..i+1]) == CountEven(s[..i]) + (if s[i] % 2 == 0 then 1 else 0)
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert CountEven(s[..1]) == CountEven([s[0]]);
  } else {
    var prefix := s[..i+1];
    var smallerPrefix := s[..i];
    assert prefix == smallerPrefix + [s[i]];
    CountEvenSuffixLemma(smallerPrefix, s[i]);
  }
}

lemma CountEvenSuffixLemma(s: seq<int>, x: int)
requires positive(s)
requires x >= 0
ensures positive(s + [x])
ensures CountEven(s + [x]) == CountEven(s) + (if x % 2 == 0 then 1 else 0)
{
  var extended := s + [x];
  assert extended[|extended|-1] == x;
  assert extended[..|extended|-1] == s;
}

lemma CountEvenComplete(s: seq<int>)
requires positive(s)
ensures CountEven(s[..|s|]) == CountEven(s)
{
  assert s[..|s|] == s;
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
    if v[i] % 2 == 0 {
      n := n + 1;
    }
    
    CountEvenIncremental(v[..], i);
    i := i + 1;
  }
  
  CountEvenComplete(v[..]);
}
// </vc-code>

