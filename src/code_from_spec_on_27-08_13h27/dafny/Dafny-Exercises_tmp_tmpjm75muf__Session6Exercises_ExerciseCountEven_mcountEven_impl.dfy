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
lemma CountEvenLemma(s: seq<int>)
  requires positive(s)
  ensures forall i :: 0 <= i < |s| ==> (s[i] % 2 == 0 ==> CountEven(s[..i+1]) == CountEven(s[..i]) + 1) && (s[i] % 2 != 0 ==> CountEven(s[..i+1]) == CountEven(s[..i]))
  decreases s
{
  if s == [] {
  } else {
    var last := s[|s|-1];
    var prefix := s[..|s|-1];
    CountEvenLemma(prefix);
    assert forall i :: 0 <= i < |prefix| ==> (prefix[i] % 2 == 0 ==> CountEven(prefix[..i+1]) == CountEven(prefix[..i]) + 1) && (prefix[i] % 2 != 0 ==> CountEven(prefix[..i+1]) == CountEven(prefix[..i]));
    if last % 2 == 0 {
      assert CountEven(s) == CountEven(prefix) + 1;
    } else {
      assert CountEven(s) == CountEven(prefix);
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mcountEven(v:array<int>) 
returns (n:int)
requires positive(v[..])
ensures  n==CountEven(v[..])
// </vc-spec>
// </vc-spec>

// <vc-code>
method CountEvenImpl(v: array<int>) 
returns (n: int)
requires positive(v[..])
ensures n == CountEven(v[..])
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
  }
}
// </vc-code>
