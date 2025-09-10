predicate ValidInput(n: int, m: int, pairs: seq<(int, int)>)
{
    n >= 2 && 
    m >= 0 && 
    |pairs| == m &&
    (forall i :: 0 <= i < |pairs| ==> 1 <= pairs[i].0 <= n && 1 <= pairs[i].1 <= n) &&
    (forall i :: 0 <= i < |pairs| ==> pairs[i].0 != pairs[i].1)
}

function computeFinalL(pairs: seq<(int, int)>): int
{
    if |pairs| == 0 then 1
    else 
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var minVal := if x < y then x else y;
        var restL := computeFinalL(pairs[..|pairs|-1]);
        if restL > minVal then restL else minVal
}

function computeFinalR(n: int, pairs: seq<(int, int)>): int
{
    if |pairs| == 0 then n
    else
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var maxVal := if x > y then x else y;
        var restR := computeFinalR(n, pairs[..|pairs|-1]);
        if restR < maxVal then restR else maxVal
}

function max(a: int, b: int): int
{
    if a > b then a else b
}

predicate ValidResult(n: int, pairs: seq<(int, int)>, result: int)
{
    result >= 0 &&
    result <= n - 1 &&
    result == max(computeFinalR(n, pairs) - computeFinalL(pairs), 0)
}

// <vc-helpers>
lemma ComputeFinalLMonotonic(pairs: seq<(int, int)>, i: int)
  requires 0 <= i < |pairs|
  ensures computeFinalL(pairs[..i+1]) >= computeFinalL(pairs[..i])
{
  if |pairs[..i]| > 0 {
    var x := pairs[i].0;
    var y := pairs[i].1;
    var minVal := if x < y then x else y;
    var prev := computeFinalL(pairs[..i]);
    assert prev >= computeFinalL(pairs[..i-1]) by { if i > 0 { ComputeFinalLMonotonic(pairs, i-1); } }
  } else {
    // Base case: empty sequence to single element
    assert computeFinalL(pairs[..0]) == 1;
    var x := pairs[0].0;
    var y := pairs[0].1;
    var minVal := if x < y then x else y;
    assert minVal >= 1;
    assert computeFinalL(pairs[..1]) == minVal;
  }
}

lemma ComputeFinalRMonotonic(n: int, pairs: seq<(int, int)>, i: int)
  requires 0 <= i < |pairs|
  ensures computeFinalR(n, pairs[..i+1]) <= computeFinalR(n, pairs[..i])
{
  if |pairs[..i]| > 0 {
    var x := pairs[i].0;
    var y := pairs[i].1;
    var maxVal := if x > y then x else y;
    var prev := computeFinalR(n, pairs[..i]);
    assert prev <= computeFinalR(n, pairs[..i-1]) by { if i > 0 { ComputeFinalRMonotonic(n, pairs, i-1); } }
  } else {
    // Base case: empty sequence to single element
    assert computeFinalR(n, pairs[..0]) == n;
    var x := pairs[0].0;
    var y := pairs[0].1;
    var maxVal := if x > y then x else y;
    assert maxVal <= n;
    assert computeFinalR(n, pairs[..1]) == maxVal;
  }
}

lemma ComputeFinalLBounds(pairs: seq<(int, int)>)
  ensures |pairs| > 0 ==> computeFinalL(pairs) >= 1
  decreases |pairs|
{
  if |pairs| > 0 {
    var x := pairs[|pairs|-1].0;
    var y := pairs[|pairs|-1].1;
    var minVal := if x < y then x else y;
    assert minVal >= 1;
    if |pairs| > 1 {
      ComputeFinalLBounds(pairs[..|pairs|-1]);
      var restL := computeFinalL(pairs[..|pairs|-1]);
      assert restL >= 1;
    }
  }
}

lemma ComputeFinalRBounds(n: int, pairs: seq<(int, int)>)
  ensures |pairs| > 0 ==> computeFinalR(n, pairs) <= n
  decreases |pairs|
{
  if |pairs| > 0 {
    var x := pairs[|pairs|-1].0;
    var y := pairs[|pairs|-1].1;
    var maxVal := if x > y then x else y;
    assert maxVal <= n;
    if |pairs| > 1 {
      ComputeFinalRBounds(n, pairs[..|pairs|-1]);
      var restR := computeFinalR(n, pairs[..|pairs|-1]);
      assert restR <= n;
    }
  }
}

lemma ComputeFinalInductiveStepL(pairs: seq<(int, int)>, i: int)
  requires 0 <= i < |pairs|
  requires var l_prev := computeFinalL(pairs[..i]);
  requires var x := pairs[i].0;
  requires var y := pairs[i].1;
  requires var minVal := if x < y then x else y;
  ensures computeFinalL(pairs[..i+1]) == (if l_prev > minVal then l_prev else minVal)
{
  // The implementation directly matches the function definition
  assert computeFinalL(pairs[..i+1]) == 
    (var x' := pairs[i].0; 
     var y' := pairs[i].1; 
     var minVal' := if x' < y' then x' else y'; 
     if computeFinalL(pairs[..i]) > minVal' then computeFinalL(pairs[..i]) else minVal');
}

lemma ComputeFinalInductiveStepR(n: int, pairs: seq<(int, int)>, i: int)
  requires 0 <= i < |pairs|
  requires var r_prev := computeFinalR(n, pairs[..i]);
  requires var x := pairs[i].0;
  requires var y := pairs[i].1;
  requires var maxVal := if x > y then x else y;
  ensures computeFinalR(n, pairs[..i+1]) == (if r_prev < maxVal then r_prev else maxVal)
{
  // The implementation directly matches the function definition
  assert computeFinalR(n, pairs[..i+1]) == 
    (var x' := pairs[i].0; 
     var y' := pairs[i].1; 
     var maxVal' := if x' > y' then x' else y'; 
     if computeFinalR(n, pairs[..i]) < maxVal' then computeFinalR(n, pairs[..i]) else maxVal');
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, pairs: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, m, pairs)
    ensures ValidResult(n, pairs, result)
// </vc-spec>
// <vc-code>
{
  var l := 1;
  var r := n;
  var i := 0;
  
  while i < m
    invariant 0 <= i <= m
    invariant 1 <= l <= n
    invariant 1 <= r <= n
    invariant l <= r
    invariant l == computeFinalL(pairs[..i])
    invariant r == computeFinalR(n, pairs[..i])
  {
    var x := pairs[i].0;
    var y := pairs[i].1;
    
    var minVal := if x < y then x else y;
    var maxVal := if x > y then x else y;
    
    ComputeFinalLBounds(pairs[..i+1]);
    ComputeFinalRBounds(n, pairs[..i+1]);
    
    if minVal > l {
      l := minVal;
    }
    
    if maxVal < r {
      r := maxVal;
    }
    
    // Prove the inductive step for l
    assert l == computeFinalL(pairs[..i+1]) by {
      ComputeFinalInductiveStepL(pairs, i);
      if computeFinalL(pairs[..i]) > minVal {
        // Case 1: previous l was larger than minVal
        assert l == computeFinalL(pairs[..i]) && computeFinalL(pairs[..i+1]) == computeFinalL(pairs[..i]);
      } else {
        // Case 2: minVal is larger or equal
        assert l == minVal && computeFinalL(pairs[..i+1]) == minVal;
      }
    }
    
    // Prove the inductive step for r
    assert r == computeFinalR(n, pairs[..i+1]) by {
      ComputeFinalInductiveStepR(n, pairs, i);
      if computeFinalR(n, pairs[..i]) < maxVal {
        // Case 1: previous r was smaller than maxVal
        assert r == computeFinalR(n, pairs[..i]) && computeFinalR(n, pairs[..i+1]) == computeFinalR(n, pairs[..i]);
      } else {
        // Case 2: maxVal is smaller or equal
        assert r == maxVal && computeFinalR(n, pairs[..i+1]) == maxVal;
      }
    }
    
    ComputeFinalLMonotonic(pairs, i);
    ComputeFinalRMonotonic(n, pairs, i);
    i := i + 1;
  }
  
  if r > l {
    result := r - l;
  } else {
    result := 0;
  }
}
// </vc-code>

