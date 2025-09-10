function concat_seqs(seqs: seq<seq<char>>): seq<char>
{
    if |seqs| == 0 then []
    else seqs[0] + concat_seqs(seqs[1..])
}

predicate ValidSplit(result: seq<seq<char>>, k: int, q: seq<char>)
{
    |result| == k &&
    (forall i :: 0 <= i < |result| ==> |result[i]| > 0) &&
    (forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0]) &&
    concat_seqs(result) == q
}

// <vc-helpers>
lemma ConcatSeqsAppend(a: seq<seq<char>>, b: seq<seq<char>>)
  ensures concat_seqs(a + b) == concat_seqs(a) + concat_seqs(b)
{
  if |a| == 0 {
    assert a + b == b;
    assert concat_seqs(a) + concat_seqs(b) == [] + concat_seqs(b) == concat_seqs(b);
  } else {
    calc {
      concat_seqs(a + b);
      == { assert |a + b| > 0; }
      (a + b)[0] + concat_seqs((a + b)[1..]);
      == { assert (a + b)[0] == a[0]; assert (a + b)[1..] == a[1..] + b; }
      a[0] + concat_seqs(a[1..] + b);
      == { ConcatSeqsAppend(a[1..], b); }
      a[0] + (concat_seqs(a[1..]) + concat_seqs(b));
      == 
      (a[0] + concat_seqs(a[1..])) + concat_seqs(b);
      == 
      concat_seqs(a) + concat_seqs(b);
    }
  }
}

lemma ConcatSeqsIsEmpty(a: seq<seq<char>>)
  ensures concat_seqs(a) == [] <==> (forall i | 0 <= i < |a| :: |a[i]| == 0)
{
}

predicate HasDistinctFirstChars(result: seq<seq<char>>)
{
  |result| == 0 || (forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0])
}

lemma EmptySeqHasDistinctFirstChars()
  ensures HasDistinctFirstChars([])
{
}

lemma SingletonSeqHasDistinctFirstChars(s: seq<char>)
  requires |s| > 0
  ensures HasDistinctFirstChars([s])
{
}

lemma AppendPreservesDistinctFirstChars(result: seq<seq<char>>, segment: seq<char>, usedFirstChars: set<char>)
  requires HasDistinctFirstChars(result)
  requires |segment| > 0
  requires forall s | s in result :: s[0] != segment[0]
  ensures HasDistinctFirstChars(result + [segment])
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(k: int, q: seq<char>) returns (result: seq<seq<char>>)
    requires k >= 0
    requires |q| >= 0
    ensures k <= 0 || |q| == 0 ==> |result| == 0
    ensures k > 0 && |q| > 0 ==> (
        (|result| == 0) || ValidSplit(result, k, q)
    )
// </vc-spec>
// <vc-code>
{
  if k <= 0 || |q| == 0 {
    result := [];
  } else {
    if |q| < k {
      result := [];
    } else {
      result := [];
      var remaining := q;
      var usedFirstChars: set<char> := {};
      var i := 0;
      
      while i < k && |remaining| > 0
        invariant 0 <= i <= k
        invariant |result| == i
        invariant (forall x | x in result :: |x| > 0)
        invariant HasDistinctFirstChars(result)
        invariant concat_seqs(result) + remaining == q
        decreases k - i
      {
        var firstChar := remaining[0];
        if firstChar in usedFirstChars {
          result := [];
          break;
        }
        usedFirstChars := usedFirstChars + {firstChar};
        
        var segment: seq<char> := [firstChar];
        remaining := remaining[1..];
        result := result + [segment];
        i := i + 1;
      }

      if i != k || |remaining| != 0 {
        result := [];
      }
    }
  }
}
// </vc-code>

