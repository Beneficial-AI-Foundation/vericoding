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
  if i > 0 {
    ComputeFinalLMonotonic(pairs, i-1);
  }
  var x := pairs[i].0;
  var y := pairs[i].1;
  var minVal := if x < y then x else y;
  var prev := computeFinalL(pairs[..i]);
  // The assertion might need to be more careful
  if prev > minVal {
    assert computeFinalL(pairs[..i+1]) == prev;
  } else {
    assert computeFinalL(pairs[..i+1]) == minVal;
    assert minVal >= prev; // Since minVal is the minimum of two numbers >=1
  }
}

lemma ComputeFinalRMonotonic(n: int, pairs: seq<(int, int)>, i: int)
  requires 0 <= i < |pairs|
  ensures computeFinalR(n, pairs[..i+1]) <= computeFinalR(n, pairs[..i])
{
  if i > 0 {
    ComputeFinalRMonotonic(n, pairs, i-1);
  }
  var x := pairs[i].0;
  var y := pairs[i].1;
  var maxVal := if x > y then x else y;
  var prev := computeFinalR(n, pairs[..i]);
  if prev < maxVal {
    assert computeFinalR(n, pairs[..i+1]) == prev;
  } else {
    assert computeFinalR(n, pairs[..i+1]) == maxVal;
    assert maxVal <= prev; // Since maxVal is the maximum of two numbers <=n
  }
}

lemma ComputeFinalLBounds(pairs: seq<(int, int)>)
  ensures computeFinalL(pairs) >= 1
  decreases |pairs|
{
  if |pairs| > 0 {
    var x := pairs[|pairs|-1].0;
    var y := pairs[|pairs|-1].1;
    var minVal := if x < y then x else y;
    assert minVal >= 1;
    ComputeFinalLBounds(pairs[..|pairs|-1]);
    var restL := computeFinalL(pairs[..|pairs|-1]);
    assert restL >= 1;
    // The result is either restL or minVal, both >= 1
  }
}

lemma ComputeFinalRBounds(n: int, pairs: seq<(int, int)>)
  ensures computeFinalR(n, pairs) <= n
  decreases |pairs|
{
  if |pairs| > 0 {
    var x := pairs[|pairs|-1].0;
    var y := pairs[|pairs|-1].1;
    var maxVal := if x > y then x else y;
    assert maxVal <= n;
    ComputeFinalRBounds(n, pairs[..|pairs|-1]);
    var restR := computeFinalR(n, pairs[..|pairs|-1]);
    assert restR <= n;
    // The result is either restR or maxVal, both <= n
  }
}

lemma ComputeFinalInductiveStepL(pairs: seq<(int, int)>, i: int)
  requires 0 <= i < |pairs|
  ensures computeFinalL(pairs[..i+1]) == 
    (var x := pairs[i].0;
     var y := pairs[i].1;
     var minVal := if x < y then x else y;
     if computeFinalL(pairs[..i]) > minVal then computeFinalL(pairs[..i]) else minVal)
{
  // The function definition ensures this
}

lemma ComputeFinalInductiveStepR(n: int, pairs: seq<(int, int)>, i: int)
  requires 0 <= i < |pairs|
  ensures computeFinalR(n, pairs[..i+1]) == 
    (var x := pairs[i].0;
     var y := pairs[i].1;
     var maxVal := if x > y then x else y;
     if computeFinalR(n, pairs[..i]) < maxVal then computeFinalR(n, pairs[..i]) else maxVal)
{
  // The function definition ensures this
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
    
    // Update l and r according to the function definitions
    var prev_l := l;
    var prev_r := r;
    
    // First prove bounds for the new values
    assert minVal >= 1;
    assert maxVal <= n;
    ComputeFinalLBounds(pairs[..i]);
    ComputeFinalRBounds(n, pairs[..i]);
    
    if prev_l > minVal {
      l := prev_l;
    } else {
      l := minVal;
    }
    
    if prev_r < maxVal {
      r := prev_r;
    } else {
      r := maxVal;
    }
    
    // Prove l <= r
    if prev_l <= prev_r {
      if prev_l > minVal && prev_r < maxVal {
        // Both unchanged
        assert l == prev_l && r == prev_r;
      } else if prev_l > minVal && prev_r >= maxVal {
        // l unchanged, r becomes maxVal
        assert l == prev_l && r == maxVal;
        assert maxVal >= minVal; // Since maxVal and minVal come from same pair
        assert prev_l <= maxVal; // Because prev_l <= prev_r <= maxVal
      } else if prev_l <= minVal && prev_r < maxVal {
        // l becomes minVal, r unchanged
        assert l == minVal && r == prev_r;
        assert minVal <= prev_r; // Because minVal <= maxVal <= prev_r
      } else { // prev_l <= minVal && prev_r >= maxVal
        // Both changed
        assert l == minVal && r == maxVal;
        assert minVal <= maxVal; // By definition of min/max
      }
    }
    
    // Prove the invariants using the lemmas
    ComputeFinalInductiveStepL(pairs, i);
    assert l == computeFinalL(pairs[..i+1]);
    
    ComputeFinalInductiveStepR(n, pairs, i);
    assert r == computeFinalR(n, pairs[..i+1]);
    
    i := i + 1;
  }
  
  if r > l {
    result := r - l;
  } else {
    result := 0;
  }
}
// </vc-code>

