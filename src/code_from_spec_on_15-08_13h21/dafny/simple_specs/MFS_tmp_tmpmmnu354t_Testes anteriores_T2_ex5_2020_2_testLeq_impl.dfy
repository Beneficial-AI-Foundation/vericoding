method leq(a: array<int>, b: array<int>) returns (result: bool) 
  ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || (exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k])
{
  /* code modified by LLM (iteration 1): Removed assume statement and implemented proper logic */
  result := false;
  
  // First check if a is a prefix of b (lexicographically smaller or equal case 1)
  if a.Length <= b.Length {
    var isPrefix := true;
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant isPrefix <==> (a[..i] == b[..i])
    {
      if a[i] != b[i] {
        isPrefix := false;
        break;
      }
      i := i + 1;
    }
    if isPrefix {
      result := true;
      return result;
    }
  }
  
  // Check for lexicographic ordering (case 2)
  var minLen := if a.Length <= b.Length then a.Length else b.Length;
  var i := 0;
  while i < minLen
    invariant 0 <= i <= minLen
    invariant a[..i] == b[..i]
  {
    if a[i] < b[i] {
      result := true;
      return result;
    } else if a[i] > b[i] {
      result := false;
      return result;
    }
    i := i + 1;
  }
  
  result := false;
}

//IMPL 
method testLeq() {
  /* code modified by LLM (iteration 1): Fixed array initialization syntax */
  var a1 := new int[3] [1, 2, 3];
  var b1 := new int[5] [1, 2, 3, 4, 5];
  var result1 := leq(a1, b1);
  
  var a2 := new int[3] [1, 2, 4];
  var b2 := new int[3] [1, 2, 3];
  var result2 := leq(a2, b2);
  
  var a3 := new int[2] [1, 2];
  var b3 := new int[2] [1, 2];
  var result3 := leq(a3, b3);
  
  // Test case where a is longer than b but starts the same
  var a4 := new int[4] [1, 2, 3, 4];
  var b4 := new int[2] [1, 2];
  var result4 := leq(a4, b4);
}