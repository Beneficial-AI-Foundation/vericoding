// <vc-preamble>
/*
 * Dafny specification for numpy.strings.join
 * 
 * This file specifies the behavior of joining characters within strings using separators.
 * For each pair of separator and sequence, the function joins the individual characters 
 * of the sequence string using the corresponding separator string.
 */

// Helper function to convert a string to a sequence of single-character strings
function StringToCharStrings(s: string): seq<string>
{
    seq(|s|, i requires 0 <= i < |s| => [s[i]])
}

// Helper function to join a sequence of strings with a separator
function JoinStrings(separator: string, strings: seq<string>): string
{
    if |strings| == 0 then ""
    else if |strings| == 1 then strings[0]
    else strings[0] + separator + JoinStrings(separator, strings[1..])
}

// Main method specification for numpy.strings.join
// </vc-preamble>

// <vc-helpers>
function SumLengths(strings: seq<string>): nat
{
    if |strings| == 0 then 0 else |strings[0]| + SumLengths(strings[1..])
}

/* helper modified by LLM (iteration 3): clarified arithmetic reasoning in recursive proof of JoinStrings length */
lemma JoinStringsLengthLemma(separator: string, strings: seq<string>)
    ensures |JoinStrings(separator, strings)| ==
              (if |strings| == 0 then 0 else SumLengths(strings) + (|strings| - 1) * |separator|)
    decreases |strings|
{
    if |strings| == 0 {
    } else if |strings| == 1 {
        assert JoinStrings(separator, strings) == strings[0];
        assert SumLengths(strings) == |strings[0]|;
    } else {
        JoinStringsLengthLemma(separator, strings[1..]);
        assert JoinStrings(separator, strings) == strings[0] + separator + JoinStrings(separator, strings[1..]);
        assert |JoinStrings(separator, strings)| == |strings[0]| + |separator| + |JoinStrings(separator, strings[1..])|;
        assert |strings[1..]| == |strings| - 1;
        assert |JoinStrings(separator, strings[1..])| == SumLengths(strings[1..]) + (|strings[1..]| - 1) * |separator|;
        assert |JoinStrings(separator, strings)| == |strings[0]| + |separator| + (SumLengths(strings[1..]) + (|strings[1..]| - 1) * |separator|);
        assert SumLengths(strings) == |strings[0]| + SumLengths(strings[1..]);
        assert |JoinStrings(separator, strings)| == SumLengths(strings) + (|strings| - 1) * |separator|;
    }
}

/* helper modified by LLM (iteration 4): removed assumes and proved tail equality via bounded forall */
lemma StringToCharStringsHead(s: string)
    requires |s| > 0
    ensures StringToCharStrings(s)[0] == [s[0]]
    ensures StringToCharStrings(s)[1..] == StringToCharStrings(s[1..])
{
    assert StringToCharStrings(s)[0] == [s[0]];
    assert |StringToCharStrings(s)| == |s|;
    assert |StringToCharStrings(s)[1..]| == |s| - 1;
    assert |StringToCharStrings(s[1..])| == |s[1..]|;
    assert |s[1..]| == |s| - 1;
    forall k | 0 <= k < |s| - 1
    ensures StringToCharStrings(s)[1..][k] == StringToCharStrings(s[1..])[k]
    {
        assert StringToCharStrings(s)[1..][k] == StringToCharStrings(s)[k + 1];
        assert StringToCharStrings(s)[k + 1] == [s[k + 1]];
        assert StringToCharStrings(s[1..])[k] == [s[1..][k]];
        assert s[1..][k] == s[k + 1];
    }
    assert StringToCharStrings(s)[1..] == StringToCharStrings(s[1..]);
}

/* helper modified by LLM (iteration 3): complete the induction step with a final equality assertion */
lemma SumLengthsCharStrings(s: string)
    ensures SumLengths(StringToCharStrings(s)) == |s|
    decreases |s|
{
    if |s| == 0 {
    } else {
        StringToCharStringsHead(s);
        SumLengthsCharStrings(s[1..]);
        assert SumLengths(StringToCharStrings(s)) == |StringToCharStrings(s)[0]| + SumLengths(StringToCharStrings(s)[1..]);
        assert |StringToCharStrings(s)[0]| == 1;
        assert SumLengths(StringToCharStrings(s)[1..]) == |s[1..]|;
        assert |s| == 1 + |s[1..]|;
        assert SumLengths(StringToCharStrings(s)) == |s|;
    }
}

lemma JoinLenCharStrings(separator: string, s: string)
    ensures (|s| == 0 ==> |JoinStrings(separator, StringToCharStrings(s))| == 0)
    ensures (|s| == 1 ==> |JoinStrings(separator, StringToCharStrings(s))| == 1)
    ensures (|s| > 1 ==> |JoinStrings(separator, StringToCharStrings(s))| == |s| + (|s| - 1) * |separator|)
{
    JoinStringsLengthLemma(separator, StringToCharStrings(s));
    SumLengthsCharStrings(s);
}

/* helper modified by LLM (iteration 4): removed assumes and proved per-index origin via bounded forall with case split */
lemma CharOriginForJoinStringsCharStrings(separator: string, s: string)
    ensures |s| > 1 ==>
        forall j :: 0 <= j < |JoinStrings(separator, StringToCharStrings(s))| ==>
            (exists k :: 0 <= k < |s| && JoinStrings(separator, StringToCharStrings(s))[j] == s[k]) ||
            (exists k :: 0 <= k < |separator| && JoinStrings(separator, StringToCharStrings(s))[j] == separator[k])
    decreases |s|
{
    if |s| > 1 {
        StringToCharStringsHead(s);
        var r := JoinStrings(separator, StringToCharStrings(s));
        var tail := JoinStrings(separator, StringToCharStrings(s[1..]));
        assert r == [s[0]] + separator + tail;
        assert |r| == 1 + |separator| + |tail|;
        forall j | 0 <= j < |r|
        ensures (exists k :: 0 <= k < |s| && r[j] == s[k]) ||
                (exists k :: 0 <= k < |separator| && r[j] == separator[k])
        {
            if j == 0 {
                assert r[j] == s[0];
                assert exists k :: 0 <= k < |s| && r[j] == s[k];
            } else if j < 1 + |separator| {
                var k2 := j - 1;
                assert 0 <= k2 < |separator|;
                assert r[j] == separator[k2];
                assert exists k :: 0 <= k < |separator| && r[j] == separator[k];
            } else {
                var j2 := j - 1 - |separator|;
                assert 0 <= j2 < |tail|;
                if |s[1..]| > 1 {
                    CharOriginForJoinStringsCharStrings(separator, s[1..]);
                    assert forall jj :: 0 <= jj < |tail| ==>
                        (exists k :: 0 <= k < |s[1..]| && tail[jj] == s[1..][k]) ||
                        (exists k :: 0 <= k < |separator| && tail[jj] == separator[k]);
                    if (exists k :: 0 <= k < |s[1..]| && tail[j2] == s[1..][k]) {
                        var k: int :| 0 <= k < |s[1..]| && tail[j2] == s[1..][k];
                        assert 0 <= k + 1 < |s|;
                        assert s[1..][k] == s[k + 1];
                        assert r[j] == tail[j2];
                        assert r[j] == s[k + 1];
                        assert exists kk :: 0 <= kk < |s| && r[j] == s[kk];
                    } else {
                        var kk: int :| 0 <= kk < |separator| && tail[j2] == separator[kk];
                        assert r[j] == tail[j2];
                        assert exists k :: 0 <= k < |separator| && r[j] == separator[k];
                    }
                } else {
                    assert |s[1..]| == 1;
                    assert tail == [s[1..][0]]; // from JoinStrings definition on single element
                    assert |tail| == 1;
                    assert j2 == 0;
                    assert s[1..][0] == s[1];
                    assert tail[0] == s[1];
                    assert r[j] == tail[0];
                    assert r[j] == s[1];
                    assert 0 <= 1 < |s|;
                    assert exists kk :: 0 <= kk < |s| && r[j] == s[kk];
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method Join(sep: seq<string>, seq_strings: seq<string>) returns (result: seq<string>)
    requires |sep| == |seq_strings|
    ensures |result| == |sep|
    ensures forall i :: 0 <= i < |result| ==>
        var s := seq_strings[i];
        var separator := sep[i];
        var expected := if |s| <= 1 then s 
                       else JoinStrings(separator, StringToCharStrings(s));
        (
            // Core correctness property
            result[i] == expected &&
            
            // Length property for non-trivial cases  
            (|s| > 1 ==> |result[i]| == |s| + (|s| - 1) * |separator|) &&
            
            // Empty string preservation
            (|s| == 0 ==> result[i] == "") &&
            
            // Single character preservation
            (|s| == 1 ==> result[i] == s) &&
            
            // Non-empty result for non-empty input
            (|s| > 0 ==> |result[i]| > 0) &&
            
            // Character order preservation - all characters in result come from original string or separator
            (|s| > 1 ==> 
                forall j :: 0 <= j < |result[i]| ==> 
                    (exists k :: 0 <= k < |s| && result[i][j] == s[k]) ||
                    (exists k :: 0 <= k < |separator| && result[i][j] == separator[k]))
        )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): added explicit requires in seq comprehension to justify indexing */
  assert |sep| == |seq_strings|;
  result := seq(|sep|, i
    requires 0 <= i < |sep| && 0 <= i < |seq_strings|
    => if |seq_strings[i]| <= 1 then seq_strings[i] else JoinStrings(sep[i], StringToCharStrings(seq_strings[i]))
  );
  assert |result| == |sep|;

  forall i | 0 <= i < |result|
  ensures
    var s := seq_strings[i];
    var separator := sep[i];
    var expected := if |s| <= 1 then s else JoinStrings(separator, StringToCharStrings(s));
    (
      result[i] == expected &&
      (|s| > 1 ==> |result[i]| == |s| + (|s| - 1) * |separator|) &&
      (|s| == 0 ==> result[i] == "") &&
      (|s| == 1 ==> result[i] == s) &&
      (|s| > 0 ==> |result[i]| > 0) &&
      (|s| > 1 ==>
        forall j :: 0 <= j < |result[i]| ==>
          (exists k :: 0 <= k < |s| && result[i][j] == s[k]) ||
          (exists k :: 0 <= k < |separator| && result[i][j] == separator[k]))
    )
  {
    var s := seq_strings[i];
    var separator := sep[i];

    // Core equality from construction
    assert result[i] == (if |s| <= 1 then s else JoinStrings(separator, StringToCharStrings(s)));

    if |s| > 1 {
      // Length property and non-emptiness
      JoinLenCharStrings(separator, s);
      assert |result[i]| == |s| + (|s| - 1) * |separator|;
      assert |result[i]| > 0;

      // Character-origin property
      assert result[i] == JoinStrings(separator, StringToCharStrings(s));
      CharOriginForJoinStringsCharStrings(separator, s);
      JoinLenCharStrings(separator, s);
      assert |result[i]| == |JoinStrings(separator, StringToCharStrings(s))|;
      forall j | 0 <= j < |result[i]|
      ensures (exists k :: 0 <= k < |s| && result[i][j] == s[k]) ||
              (exists k :: 0 <= k < |separator| && result[i][j] == separator[k])
      {
        assert 0 <= j < |JoinStrings(separator, StringToCharStrings(s))|;
        assert (exists k :: 0 <= k < |s| && JoinStrings(separator, StringToCharStrings(s))[j] == s[k]) ||
               (exists k :: 0 <= k < |separator| && JoinStrings(separator, StringToCharStrings(s))[j] == separator[k]);
        assert result[i] == JoinStrings(separator, StringToCharStrings(s));
      }
    } else if |s| == 1 {
      assert result[i] == s;
      assert |result[i]| > 0;
    } else {
      assert |s| == 0;
      assert result[i] == "";
    }
  }
}
// </vc-code>
