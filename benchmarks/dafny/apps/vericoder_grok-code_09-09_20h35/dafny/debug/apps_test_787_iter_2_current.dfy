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
if k <= 0 || |q| == 0 {
    result := [];
  } else {
    var used: set<char> := {};
    var starts: seq<int> := [0];
    var i := 1;
    var success := true;
    while |starts| < k && success
      decreases k - |starts|
    {
      var found := false;
      while i < |q| && !found {
        if q[i] !in used {
          used := used + {q[i]};
          starts := starts + [i];
          found := true;
        }
        i := i + 1;
      }
      if !found {
        success := false;
        result := [];
      }
    }
    if success {
      result := [];
      var j := 0;
      while j < k {
        var next := if j + 1 < k then starts[j + 1] else |q|;
        result := result + [q[starts[j] .. next]];
        j := j + 1;
      }
    } else {
      // result already set to empty
    }
  }
// </vc-code>

