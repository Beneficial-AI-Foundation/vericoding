// <vc-preamble>
// Method that creates a 2-D array by stacking two vectors as columns
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): lemma for length after concatenation */
lemma ConcatSingleLength<T>(s: seq<T>, x: T) ensures |s + [x]| == |s| + 1 {
  calc {
    |s + [x]|;
    == { }
    |s| + |[x]|;
    == { }
    |s| + 1;
  }
}

/* helper modified by LLM (iteration 4): lemma that a pair has length 2 */
lemma PairLength<T>(x: T, y: T) ensures |[x,y]| == 2 {
  calc {
    |[x,y]|;
    == { }
    |[x]| + |[y]|;
    == { }
    1 + 1;
    == { }
    2;
  }
}

/* helper modified by LLM (iteration 4): lemma that last element of s+[x] is x */
lemma LastConcat<T>(s: seq<T>, x: T) ensures (s + [x])[|s|] == x {
  calc {
    (s + [x])[|s|];
    == { }
    [x][|s| - |s|];
    == { }
    [x][0];
    == { }
    x;
  }
}

// </vc-helpers>

// <vc-spec>
method c_(arr1: seq<real>, arr2: seq<real>) returns (result: seq<seq<real>>)
  // Precondition: input arrays must have the same length
  requires |arr1| == |arr2|
  
  // Postconditions: result structure and content
  ensures |result| == |arr1|  // result has same number of rows as input length
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == 2  // each row has exactly 2 columns
  ensures forall i :: 0 <= i < |result| ==> 
    result[i][0] == arr1[i] && result[i][1] == arr2[i]  // correct column placement
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): build 2D result by appending rows [arr1[i], arr2[i]] */
{
  var n := |arr1|;
  var i := 0;
  result := [];
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> |result[j]| == 2 && result[j][0] == arr1[j] && result[j][1] == arr2[j]
  {
    var oldResult := result;
    var row := [arr1[i], arr2[i]];
    ConcatSingleLength(oldResult, row);
    result := oldResult + [row];
    LastConcat(oldResult, row);
    PairLength(arr1[i], arr2[i]);
    assert result[i] == row;
    assert result[i][0] == arr1[i] && result[i][1] == arr2[i];
    i := i + 1;
  }
}
// </vc-code>
