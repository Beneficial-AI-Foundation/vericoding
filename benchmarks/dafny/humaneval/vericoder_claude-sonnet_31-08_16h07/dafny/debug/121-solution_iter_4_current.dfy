

// <vc-helpers>
lemma SumProperty(s: seq<int>, p: seq<bool>, i: int)
  requires |s| == |p|
  requires 0 <= i <= |s|
  ensures sum(s, p) == sum(s[..i], p[..i]) + sum(s[i..], p[i..])
{
  if i == 0 {
    assert s[..0] == [];
    assert p[..0] == [];
    assert sum(s[..0], p[..0]) == 0;
    assert s[0..] == s;
    assert p[0..] == p;
  } else if i == |s| {
    assert s[i..] == [];
    assert p[i..] == [];
    assert sum(s[i..], p[i..]) == 0;
    assert s[..|s|] == s;
    assert p[..|p|] == p;
  } else {
    assert s == [s[0]] + s[1..];
    assert p == [p[0]] + p[1..];
    assert s[..i] == [s[0]] + s[1..][..i-1];
    assert p[..i] == [p[0]] + p[1..][..i-1];
    assert s[i..] == s[1..][i-1..];
    assert p[i..] == p[1..][i-1..];
    SumProperty(s[1..], p[1..], i-1);
  }
}

lemma SumIncremental(s: seq<int>, p: seq<bool>, i: int)
  requires |s| == |p|
  requires 0 <= i < |s|
  ensures sum(s[..i+1], p[..i+1]) == sum(s[..i], p[..i]) + (if p[i] then s[i] else 0)
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert p[..1] == [p[0]];
    assert s[..0] == [];
    assert p[..0] == [];
    assert sum(s[..0], p[..0]) == 0;
  } else {
    assert s[..i+1] == [s[0]] + s[1..][..i];
    assert p[..i+1] == [p[0]] + p[1..][..i];
    assert s[..i] == [s[0]] + s[1..][..i-1];
    assert p[..i] == [p[0]] + p[1..][..i-1];
    SumIncremental(s[1..], p[1..], i-1);
  }
}
// </vc-helpers>

// <vc-spec>
method solution(numbers: seq<int>) returns (s: int)
  // post-conditions-start
  ensures s == sum(numbers, seq(|numbers|, i requires 0 <= i < |numbers| => i % 2 == 0 && numbers[i] % 2 == 1))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  s := 0;
  var i := 0;
  
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant s == sum(numbers[..i], seq(i, j requires 0 <= j < i => j % 2 == 0 && numbers[j] % 2 == 1))
  {
    var condition := i % 2 == 0 && numbers[i] % 2 == 1;
    var oldPredSeq := seq(i, j requires 0 <= j < i => j % 2 == 0 && numbers[j] % 2 == 1);
    var newPredSeq := seq(i+1, j requires 0 <= j < i+1 => j % 2 == 0 && numbers[j] % 2 == 1);
    
    assert |numbers[..i]| == |oldPredSeq|;
    assert |numbers[..i+1]| == |newPredSeq|;
    assert numbers[..i+1] == numbers[..i] + [numbers[i]];
    assert newPredSeq == oldPredSeq + [condition];
    
    SumIncremental(numbers[..i+1], newPredSeq, i);
    
    if condition {
      s := s + numbers[i];
    }
    
    i := i + 1;
  }
  
  assert i == |numbers|;
  assert numbers[..i] == numbers;
  var finalPredSeq := seq(|numbers|, j requires 0 <= j < |numbers| => j % 2 == 0 && numbers[j] % 2 == 1);
  assert seq(i, j requires 0 <= j < i => j % 2 == 0 && numbers[j] % 2 == 1) == finalPredSeq;
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end