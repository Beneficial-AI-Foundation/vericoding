// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate capturing per-element Find specification used in invariants and assertions */
predicate IsFindResult(ai: string, subi: string, si: int, ei: int, res: int)
{
  (|subi| == 0 ==> res == si) &&
  (si + |subi| > |ai| ==> res == -1) &&
  (si > ei ==> res == -1) &&
  (|subi| > 0 && si + |subi| <= |ai| && si <= ei ==> (
    (res == -1 <==>
      (forall pos {:trigger ai[pos..pos + |subi|]} :: si <= pos <= ei && pos + |subi| <= |ai| ==> ai[pos..pos + |subi|] != subi)) &&
    (res >= 0 ==> (
      si <= res <= ei &&
      res + |subi| <= |ai| &&
      ai[res..res + |subi|] == subi &&
      (forall pos {:trigger ai[pos..pos + |subi|]} :: si <= pos < res && pos + |subi| <= |ai| ==> ai[pos..pos + |subi|] != subi)))))
}

/* helper modified by LLM (iteration 5): arithmetic lemma relating feasible slice bounds to index ordering */
lemma PosLtFromSliceBounds(pos: int, p: int, L: int, n: int)
  requires 0 <= L
  ensures (pos + L <= n && p + L > n) ==> pos < p
{
  if pos + L <= n && p + L > n {
    assert pos <= n - L;
    assert p > n - L;
    assert pos < p;
  }
}
// </vc-helpers>

// <vc-spec>
method Find(a: seq<string>, sub: seq<string>, start: seq<int>, endPos: seq<int>) 
    returns (result: seq<int>)
    // Input arrays must have the same length
    requires |a| == |sub| == |start| == |endPos|
    // Start and end positions must be valid for each string
    requires forall i :: 0 <= i < |a| ==> 
        0 <= start[i] <= endPos[i] < |a[i]|
    
    // Output has same length as inputs
    ensures |result| == |a|
    
    // Main specification for each element
    ensures forall i :: 0 <= i < |result| ==> (
        // Special cases (these take precedence)
        (|sub[i]| == 0 ==> result[i] == start[i]) &&
        (start[i] + |sub[i]| > |a[i]| ==> result[i] == -1) &&
        (start[i] > endPos[i] ==> result[i] == -1) &&
        
        // General cases only apply when special cases don't
        (|sub[i]| > 0 && start[i] + |sub[i]| <= |a[i]| && start[i] <= endPos[i] ==> (
            // Case 1: substring not found (returns -1)
            (result[i] == -1 <==> 
                (forall pos {:trigger a[i][pos..pos + |sub[i]|]} :: start[i] <= pos <= endPos[i] && pos + |sub[i]| <= |a[i]| ==>
                    a[i][pos..pos + |sub[i]|] != sub[i])) &&
            
            // Case 2: substring found (returns non-negative index)
            (result[i] >= 0 ==> (
                // Result is within valid range
                start[i] <= result[i] <= endPos[i] &&
                result[i] + |sub[i]| <= |a[i]| &&
                // Substring actually found at this position
                a[i][result[i]..result[i] + |sub[i]|] == sub[i] &&
                // This is the LOWEST index where substring is found (minimality)
                (forall pos {:trigger a[i][pos..pos + |sub[i]|]} :: start[i] <= pos < result[i] && pos + |sub[i]| <= |a[i]| ==>
                    a[i][pos..pos + |sub[i]|] != sub[i])))
        ))
    )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Implement sequential search per element with clear invariants and predicate-based spec */
  var r: seq<int> := [];
  var i := 0;
  var n := |a|;
  while i < n
    invariant 0 <= i <= n
    invariant n == |a|
    invariant |r| == i
    invariant forall j :: 0 <= j < |r| ==> IsFindResult(a[j], sub[j], start[j], endPos[j], r[j])
    decreases n - i
  {
    var ai := a[i];
    var subi := sub[i];
    var si := start[i];
    var ei := endPos[i];
    var res := -1;

    if |subi| == 0 {
      res := si;
      assert IsFindResult(ai, subi, si, ei, res);
    } else if si + |subi| > |ai| {
      res := -1;
      assert IsFindResult(ai, subi, si, ei, res);
    } else if si > ei {
      res := -1;
      assert IsFindResult(ai, subi, si, ei, res);
    } else {
      var p := si;
      while p <= ei
        invariant si <= p <= ei + 1
        invariant 0 <= |subi|
        invariant res == -1 ==> (forall q {:trigger ai[q..q + |subi|]} :: si <= q < p && q + |subi| <= |ai| ==> ai[q..q + |subi|] != subi)
        invariant res != -1 ==> (si <= res < p && res + |subi| <= |ai| && ai[res..res + |subi|] == subi &&
                                  (forall q {:trigger ai[q..q + |subi|]} :: si <= q < res && q + |subi| <= |ai| ==> ai[q..q + |subi|] != subi))
        decreases ei - p + 1
      {
        if res == -1 && p + |subi| <= |ai| && ai[p..p + |subi|] == subi {
          res := p;
        }
        p := p + 1;
      }
      assert p == ei + 1;
      if res == -1 {
        assert (forall pos {:trigger ai[pos..pos + |subi|]} :: si <= pos <= ei && pos + |subi| <= |ai| ==> ai[pos..pos + |subi|] != subi);
      } else {
        assert si <= res <= ei;
        assert res + |subi| <= |ai|;
        assert ai[res..res + |subi|] == subi;
        assert (forall pos {:trigger ai[pos..pos + |subi|]} :: si <= pos < res && pos + |subi| <= |ai| ==> ai[pos..pos + |subi|] != subi);
      }
      assert IsFindResult(ai, subi, si, ei, res);
    }

    r := r + [res];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
