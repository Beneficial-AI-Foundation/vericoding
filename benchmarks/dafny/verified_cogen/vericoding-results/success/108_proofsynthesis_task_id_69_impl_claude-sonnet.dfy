// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsArrayMatch(main: array<int>, sub: array<int>, start: int)
  reads main, sub
  requires 0 <= start <= main.Length - sub.Length
  requires sub.Length <= main.Length
{
  forall j :: 0 <= j < sub.Length ==> main[start + j] == sub[j]
}

lemma ArraySliceEquality(main: array<int>, sub: array<int>, start: int)
  requires 0 <= start <= main.Length - sub.Length
  requires sub.Length <= main.Length
  ensures IsArrayMatch(main, sub, start) <==> main[start..start+sub.Length] == sub[..]
{
}

/* helper modified by LLM (iteration 3): Added lemma to connect array match to postcondition */
lemma ArrayMatchImpliesExists(main: array<int>, sub: array<int>, start: int)
  requires 0 <= start <= main.Length - sub.Length
  requires sub.Length <= main.Length
  requires IsArrayMatch(main, sub, start)
  ensures exists k: int, l: int :: 0 <= k <= (main.Length - sub.Length) && l == k + sub.Length && (main[k..l]) == sub[..]
{
  ArraySliceEquality(main, sub, start);
  assert main[start..start+sub.Length] == sub[..];
}
// </vc-helpers>

// <vc-spec>
method IsSubList(main: array<int>, sub: array<int>) returns (result: bool)

    requires
        sub.Length <= main.Length

    ensures
        result == (exists k: int, l: int ::
            0 <= k <= (main.Length - sub.Length) && l == k + sub.Length && (main[k..l]) == sub[..])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Added proof for false case and fixed empty array case */
  if sub.Length == 0 {
    result := true;
    assert main[0..0] == sub[..];
    return;
  }
  
  var i := 0;
  while i <= main.Length - sub.Length
    invariant 0 <= i <= main.Length - sub.Length + 1
    invariant forall k: int {:trigger IsArrayMatch(main, sub, k)} :: 0 <= k < i ==> !IsArrayMatch(main, sub, k)
  {
    var matches := true;
    var j := 0;
    while j < sub.Length && matches
      invariant 0 <= j <= sub.Length
      invariant matches <==> (forall idx: int :: 0 <= idx < j ==> main[i+idx] == sub[idx])
    {
      if main[i + j] != sub[j] {
        matches := false;
      }
      j := j + 1;
    }
    
    if matches {
      assert IsArrayMatch(main, sub, i);
      ArrayMatchImpliesExists(main, sub, i);
      result := true;
      return;
    }
    
    assert !IsArrayMatch(main, sub, i);
    i := i + 1;
  }
  
  assert forall k: int :: 0 <= k <= main.Length - sub.Length ==> !IsArrayMatch(main, sub, k);
  forall k: int, l: int | 0 <= k <= (main.Length - sub.Length) && l == k + sub.Length
    ensures main[k..l] != sub[..]
  {
    ArraySliceEquality(main, sub, k);
  }
  result := false;
}
// </vc-code>
