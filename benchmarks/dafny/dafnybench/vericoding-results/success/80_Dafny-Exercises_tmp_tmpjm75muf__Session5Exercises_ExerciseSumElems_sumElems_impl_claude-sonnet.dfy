function SumR(s:seq<int>):int
decreases s
{
    if (s==[]) then 0
    else SumR(s[..|s|-1])+s[|s|-1]
}

function SumL(s:seq<int>):int
decreases s
{
    if (s==[]) then 0
    else s[0]+SumL(s[1..])
}


function SumV(v:array<int>,c:int,f:int):int
  requires 0<=c<=f<=v.Length
  reads v
  {
    SumR(v[c..f])
  }

// <vc-helpers>
lemma SumREquivalence(s: seq<int>)
  ensures SumR(s) == SumL(s)
  decreases |s|
{
  if s == [] {
    // Base case: both return 0
  } else {
    // Inductive case
    SumREquivalence(s[1..]);
    // Now we know SumR(s[1..]) == SumL(s[1..])
    // We need to show SumR(s) == SumL(s)
    // SumR(s) = SumR(s[..|s|-1]) + s[|s|-1]
    // SumL(s) = s[0] + SumL(s[1..])
    // We need to show SumR(s[..|s|-1]) + s[|s|-1] == s[0] + SumL(s[1..])
    // Since SumR(s[1..]) == SumL(s[1..]), we need SumR(s[..|s|-1]) + s[|s|-1] == s[0] + SumR(s[1..])
    SumRShift(s);
  }
}

lemma SumRShift(s: seq<int>)
  requires |s| > 0
  ensures SumR(s[..|s|-1]) + s[|s|-1] == s[0] + SumR(s[1..])
  decreases |s|
{
  if |s| == 1 {
    assert s[..|s|-1] == [];
    assert s[1..] == [];
    assert SumR([]) == 0;
  } else {
    // Inductive case: |s| >= 2
    var tail := s[1..];
    assert |tail| == |s| - 1;
    assert |tail| > 0;
    
    // Apply induction hypothesis to tail
    SumRShift(tail);
    // This gives us: SumR(tail[..|tail|-1]) + tail[|tail|-1] == tail[0] + SumR(tail[1..])
    
    // Now relate the pieces back to s
    assert tail[..|tail|-1] == s[1..|s|-1];
    assert tail[|tail|-1] == s[|s|-1];
    assert tail[0] == s[1];
    assert tail[1..] == s[2..];
    
    // So we have: SumR(s[1..|s|-1]) + s[|s|-1] == s[1] + SumR(s[2..])
    
    // We need to show: SumR(s[..|s|-1]) + s[|s|-1] == s[0] + SumR(s[1..])
    // Note that s[..|s|-1] == [s[0]] + s[1..|s|-1]
    assert s[..|s|-1] == [s[0]] + s[1..|s|-1];
    
    // Apply SumR concatenation property
    SumRConcatenation([s[0]], s[1..|s|-1]);
    assert SumR(s[..|s|-1]) == SumR([s[0]]) + SumR(s[1..|s|-1]);
    assert SumR([s[0]]) == s[0];
    
    // So SumR(s[..|s|-1]) == s[0] + SumR(s[1..|s|-1])
    // And we know SumR(s[1..|s|-1]) + s[|s|-1] == s[1] + SumR(s[2..])
    // Also, SumR(s[1..]) == s[1] + SumR(s[2..]) by definition
    
    // Therefore: SumR(s[..|s|-1]) + s[|s|-1] == s[0] + SumR(s[1..|s|-1]) + s[|s|-1]
    //                                        == s[0] + (s[1] + SumR(s[2..]))
    //                                        == s[0] + SumR(s[1..])
  }
}

lemma SumLEquivalence(s: seq<int>)
  ensures SumL(s) == SumR(s)
  decreases |s|
{
  SumREquivalence(s);
}

lemma SumRIterative(v: array<int>, i: int, acc: int)
  requires 0 <= i <= v.Length
  requires acc == SumR(v[..i])
  ensures acc + SumR(v[i..]) == SumR(v[..])
{
  if i == 0 {
    assert v[..i] == [];
    assert acc == 0;
    assert v[i..] == v[..];
  } else if i == v.Length {
    assert v[i..] == [];
    assert SumR(v[i..]) == 0;
    assert v[..] == v[..i];
  } else {
    assert v[..] == v[..i] + v[i..];
    SumRConcatenation(v[..i], v[i..]);
  }
}

lemma SumRConcatenation(s1: seq<int>, s2: seq<int>)
  ensures SumR(s1 + s2) == SumR(s1) + SumR(s2)
  decreases |s2|
{
  if s2 == [] {
    assert s1 + s2 == s1;
  } else if s1 == [] {
    assert s1 + s2 == s2;
  } else {
    var combined := s1 + s2;
    assert combined[..|combined|-1] == s1 + s2[..|s2|-1];
    assert combined[|combined|-1] == s2[|s2|-1];
    SumRConcatenation(s1, s2[..|s2|-1]);
  }
}
// </vc-helpers>

// <vc-spec>
method sumElems(v:array<int>) returns (sum:int)
//ensures sum==SumL(v[0..v.Length])
ensures sum==SumR(v[..])
//ensures sum==SumV(v,0,v.Length)
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == SumR(v[..i])
  {
    sum := sum + v[i];
    i := i + 1;
    
    assert v[..i-1] + [v[i-1]] == v[..i];
    SumRConcatenation(v[..i-1], [v[i-1]]);
    assert SumR([v[i-1]]) == v[i-1];
  }
  
  assert i == v.Length;
  assert v[..i] == v[..];
}
// </vc-code>

