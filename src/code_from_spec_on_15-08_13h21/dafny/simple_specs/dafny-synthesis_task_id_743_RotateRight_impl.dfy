//IMPL
method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
  requires n >= 0
  ensures |r| == |l|
  ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{
  if |l| == 0 {
    r := [];
    return;
  }
  
  /* code modified by LLM (iteration 4): simplified approach with direct construction */
  var effectiveRotation := n % |l|;
  var splitPoint := |l| - effectiveRotation;
  
  r := l[splitPoint..] + l[..splitPoint];
  
  // Use focused helper lemma
  RotationCorrectnessLemma(l, n, effectiveRotation, splitPoint, r);
}

/* code modified by LLM (iteration 4): streamlined correctness lemma */
lemma RotationCorrectnessLemma(l: seq<int>, n: int, effectiveRotation: int, splitPoint: int, r: seq<int>)
  requires |l| > 0
  requires n >= 0
  requires effectiveRotation == n % |l|
  requires splitPoint == |l| - effectiveRotation
  requires r == l[splitPoint..] + l[..splitPoint]
  requires |r| == |l|
  ensures forall i {:trigger r[i]} :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
{
  forall i | 0 <= i < |l|
    ensures r[i] == l[(i - n + |l|) % |l|]
  {
    if i < effectiveRotation {
      /* code modified by LLM (iteration 4): case 1 - elements from tail of original */
      assert r[i] == l[splitPoint + i];
      var targetIndex := (i - n + |l|) % |l|;
      assert targetIndex == i - n + |l|; // since i < effectiveRotation means i - n < 0
      assert i - n + |l| == splitPoint + i;
    } else {
      /* code modified by LLM (iteration 4): case 2 - elements from head of original */
      assert r[i] == l[i - effectiveRotation];
      var targetIndex := (i - n + |l|) % |l|;
      assert targetIndex == i - effectiveRotation; // direct modulo reduction
    }
  }
}