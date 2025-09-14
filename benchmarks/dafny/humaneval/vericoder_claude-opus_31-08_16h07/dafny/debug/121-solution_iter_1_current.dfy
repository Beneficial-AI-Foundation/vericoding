

// <vc-helpers>
lemma sum_prop(s: seq<int>, p: seq<bool>)
  requires |s| == |p| > 0
  ensures sum(s, p) == (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
{
}

lemma sum_extensionality(s: seq<int>, p: seq<bool>, s': seq<int>, p': seq<bool>)
  requires |s| == |p|
  requires |s'| == |p'|
  requires |s| == |s'|
  requires forall i :: 0 <= i < |s| ==> s[i] == s'[i] && p[i] == p'[i]
  ensures sum(s, p) == sum(s', p')
{
  if |s| == 0 {
  } else {
    sum_extensionality(s[1..], p[1..], s'[1..], p'[1..]);
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
    if i % 2 == 0 && numbers[i] % 2 == 1 {
      s := s + numbers[i];
    }
    
    assert numbers[..i+1] == numbers[..i] + [numbers[i]];
    var p_old := seq(i, j requires 0 <= j < i => j % 2 == 0 && numbers[j] % 2 == 1);
    var p_new := seq(i+1, j requires 0 <= j < i+1 => j % 2 == 0 && numbers[j] % 2 == 1);
    
    assert |p_new| == i + 1;
    assert forall j :: 0 <= j < i ==> p_new[j] == p_old[j];
    assert p_new[i] == (i % 2 == 0 && numbers[i] % 2 == 1);
    
    calc {
      sum(numbers[..i+1], p_new);
    == { assert p_new == p_old + [p_new[i]]; 
         assert numbers[..i+1] == numbers[..i] + [numbers[i]];
         assert sum(numbers[..i] + [numbers[i]], p_old + [p_new[i]]) == 
                sum(numbers[..i], p_old) + (if p_new[i] then numbers[i] else 0);
       }
      sum(numbers[..i], p_old) + (if p_new[i] then numbers[i] else 0);
    == 
      s + (if i % 2 == 0 && numbers[i] % 2 == 1 then numbers[i] else 0);
    }
    
    i := i + 1;
  }
  
  assert numbers[..|numbers|] == numbers;
  var p_final := seq(|numbers|, j requires 0 <= j < |numbers| => j % 2 == 0 && numbers[j] % 2 == 1);
  assert s == sum(numbers, p_final);
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end