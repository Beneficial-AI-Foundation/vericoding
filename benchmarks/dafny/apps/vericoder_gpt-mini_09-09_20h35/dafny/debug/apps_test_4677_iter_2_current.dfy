predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 10 && forall i :: 0 <= i < |s| ==> s[i] in {'0', '1', 'B'}
}

function SimulateKeystrokes(keystrokes: string): string
{
    if |keystrokes| == 0 then ""
    else 
        var prev := SimulateKeystrokes(keystrokes[..|keystrokes|-1]);
        var lastKey := keystrokes[|keystrokes|-1];
        if lastKey == 'B' then
            if |prev| > 0 then prev[..|prev|-1] else prev
        else
            prev + [lastKey]
}

predicate ValidOutput(result: string)
{
    forall i :: 0 <= i < |result| ==> result[i] in {'0', '1'}
}

// <vc-helpers>
lemma SimulateKeystrokesAppend(ks: string, ch: char)
  ensures SimulateKeystrokes(ks + [ch]) ==
    (if ch == 'B' then if |SimulateKeystrokes(ks)| > 0 then SimulateKeystrokes(ks)[..|SimulateKeystrokes(ks)|-1] else SimulateKeystrokes(ks) else SimulateKeystrokes(ks) + [ch])
{
  // By unfolding the definition of SimulateKeystrokes on ks + [ch], the equality holds.
}

lemma SimulateProducesOnly01(ks: string)
  requires forall j :: 0 <= j < |ks| ==> ks[j] in {'0','1','B'}
  ensures ValidOutput(SimulateKeystrokes(ks))
  decreases |ks|
{
  if |ks| == 0 {
    // SimulateKeystrokes("") == "" and ValidOutput("") holds vacuously
  } else {
    var prev := ks[..|ks|-1];
    var last := ks[|ks|-1];
    // Inductive hypothesis
    SimulateProducesOnly01(prev);
    var prevRes := SimulateKeystrokes(prev);

    // Compute SimulateKeystrokes(ks) using the append lemma
    SimulateKeystrokesAppend(prev, last);
    var cur := SimulateKeystrokes(ks);

    if last == 'B' {
      if |prevRes| > 0 {
        // prevRes[..|prevRes|-1] has only '0'/'1' characters because prevRes does
        assert forall i :: 0 <= i < |prevRes[..|prevRes|-1]| ==> prevRes[..|prevRes|-1][i] in {'0','1'};
        // So cur = prevRes[..|prevRes|-1] is ValidOutput
      } else {
        // prevRes == "" and cur == prevRes == "" is ValidOutput
      }
    } else {
      // last in {'0','1'} by the requires on ks
      assert last in {'0','1'};
      // prevRes + [last] contains only '0'/'1' since prevRes does and last does
      assert forall i :: 0 <= i < |prevRes + [last]| ==> (prevRes + [last])[i] in {'0','1'};
      // So cur = prevRes + [last] is ValidOutput
    }
    // Conclude ValidOutput(cur)
    assert forall i :: 0 <= i < |cur| ==> cur[i] in {'0','1'};
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(result)
    ensures result == SimulateKeystrokes(s)
// </vc-spec>
// <vc-code>
{
  var res := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|;
    invariant res == SimulateKeystrokes(s[..i]);
    invariant ValidOutput(res);
  {
    assert 0 <= i < |s|;
    ghost var prev := res;
    var ch := s[i];

    // Use the append lemma to relate SimulateKeystrokes(s[..i+1]) to SimulateKeystrokes(s[..i])
    SimulateKeystrokesAppend(s[..i], ch);

    if ch == 'B' {
      if |prev| > 0 {
        // remove last character from previous result
        res := prev[..|prev|-1];
        // now res equals the simulated result after processing this 'B'
        assert res == SimulateKeystrokes(s[..i+1]);
      } else {
        // prev is empty, nothing changes
        res := prev;
        assert res == SimulateKeystrokes(s[..i+1]);
      }
    } else {
      // ch is '0' or '1' (by ValidInput(s) and 0 <= i < |s|), append it
      res := prev + [ch];
      assert res == SimulateKeystrokes(s[..i+1]);
    }

    // From equality with SimulateKeystrokes of the prefix, derive ValidOutput for res
    SimulateProducesOnly01(s[..i+1]);
    assert ValidOutput(SimulateKeystrokes(s[..i+1]));
    assert ValidOutput(res);

    i := i + 1;
  }
  result := res;
}
// </vc-code>

