

// <vc-helpers>
lemma SumProperty(s: seq<int>, p: seq<bool>, i: int)
  requires |s| == |p|
  requires 0 <= i <= |s|
  ensures sum(s, p) == sum(s[..i], p[..i]) + sum(s[i..], p[i..])
{
  if i == 0 {
    assert s[..0] == [];
    assert p[..0] == [];
    assert s[0..] == s;
    assert p[0..] == p;
  } else if i == |s| {
    assert s[i..] == [];
    assert p[i..] == [];
  } else {
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
  } else {
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
    if condition {
      s := s + numbers[i];
    }
    
    SumIncremental(numbers[..i+1], seq(i+1, j requires 0 <= j < i+1 => j % 2 == 0 && numbers[j] % 2 == 1), i);
    
    i := i + 1;
  }
  
  assert numbers[..i] == numbers;
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end