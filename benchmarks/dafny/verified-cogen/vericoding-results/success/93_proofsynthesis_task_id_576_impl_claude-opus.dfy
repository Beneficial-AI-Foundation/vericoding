// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to prove non-existence of subarray */
predicate IsSubArrayAt(main: array<int>, sub: array<int>, k: int)
  requires 0 <= k <= main.Length - sub.Length
  requires sub.Length <= main.Length
  reads main, sub
{
  forall i :: 0 <= i < sub.Length ==> main[k + i] == sub[i]
}

lemma IsSubArrayAtImpliesSliceEqual(main: array<int>, sub: array<int>, k: int)
  requires 0 <= k <= main.Length - sub.Length
  requires sub.Length <= main.Length
  requires IsSubArrayAt(main, sub, k)
  ensures main[k..k+sub.Length] == sub[..]
{
  assert forall i :: 0 <= i < sub.Length ==> main[k..k+sub.Length][i] == sub[..][i];
}

lemma NoSubArrayImpliesNotExists(main: array<int>, sub: array<int>, bound: int)
  requires sub.Length <= main.Length
  requires 0 <= bound <= main.Length - sub.Length + 1
  requires forall k :: 0 <= k < bound ==> !IsSubArrayAt(main, sub, k)
  ensures !(exists k: int, l: int :: 0 <= k < bound && l == k + sub.Length && main[k..l] == sub[..])
{
  if exists k: int, l: int :: 0 <= k < bound && l == k + sub.Length && main[k..l] == sub[..] {
    var k: int, l: int :| 0 <= k < bound && l == k + sub.Length && main[k..l] == sub[..];
    assert forall i :: 0 <= i < sub.Length ==> main[k + i] == sub[i];
    assert IsSubArrayAt(main, sub, k);
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method IsSubArray(main: array<int>, sub: array<int>) returns (result: bool)
    requires sub.Length <= main.Length
    ensures result == (exists k: int, l: int ::
        0 <= k <= (main.Length - sub.Length) && l == k + sub.Length && 
        main[k..l] == sub[..])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed postcondition for empty subarray case and added lemma call for false case */
{
  if sub.Length == 0 {
    assert main[0..0] == sub[..];
    assert exists k: int, l: int :: 0 <= k <= main.Length - sub.Length && l == k + sub.Length && main[k..l] == sub[..];
    return true;
  }
  
  var i := 0;
  while i <= main.Length - sub.Length
    invariant 0 <= i <= main.Length - sub.Length + 1
    invariant forall k :: 0 <= k < i ==> !IsSubArrayAt(main, sub, k)
  {
    var j := 0;
    var found := true;
    while j < sub.Length
      invariant 0 <= j <= sub.Length
      invariant found == (forall m :: 0 <= m < j ==> main[i + m] == sub[m])
    {
      if main[i + j] != sub[j] {
        found := false;
        break;
      }
      j := j + 1;
    }
    
    if found {
      assert IsSubArrayAt(main, sub, i);
      IsSubArrayAtImpliesSliceEqual(main, sub, i);
      assert main[i..i+sub.Length] == sub[..];
      assert exists k: int, l: int :: 0 <= k <= main.Length - sub.Length && l == k + sub.Length && main[k..l] == sub[..];
      return true;
    }
    i := i + 1;
  }
  
  NoSubArrayImpliesNotExists(main, sub, main.Length - sub.Length + 1);
  assert !(exists k: int, l: int :: 0 <= k <= main.Length - sub.Length && l == k + sub.Length && main[k..l] == sub[..]);
  return false;
}
// </vc-code>
