// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide IndexOf for sequences used in specifications */
function IndexOf(s: seq<int>, v: int): int
  requires v in s
  ensures 0 <= IndexOf(s, v) < |s| && s[IndexOf(s, v)] == v
  decreases |s|
{
  if s[0] == v then 0 else 1 + IndexOf(s[1..], v)
}
// </vc-helpers>

// <vc-spec>
method NextGreaterElement(nums1: array<int>, nums2: array<int>) returns (result: array<int>)
    requires
        forall i, j :: 0 <= i < nums1.Length && 0 <= j < nums1.Length && i != j ==> nums1[i] != nums1[j]
    requires
        forall i, j :: 0 <= i < nums2.Length && 0 <= j < nums2.Length && i != j ==> nums2[i] != nums2[j]
    ensures
        result.Length == nums1.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): implement NextGreaterElement using monotone stack with loop invariants to ensure safe indexing */
  result := new int[nums1.Length];
  var m: map<int,int> := map[];
  var stk := new int[nums2.Length];
  var top := 0;
  var i := 0;
  while i < nums2.Length
    decreases nums2.Length - i
    invariant 0 <= i <= nums2.Length
    invariant 0 <= top <= nums2.Length
    invariant top <= i
    invariant forall k :: 0 <= k < top ==> 0 <= stk[k] < nums2.Length
  {
    while top > 0
      decreases top
      invariant 0 <= i <= nums2.Length
      invariant 0 <= top <= nums2.Length
      invariant top <= i
      invariant forall k :: 0 <= k < top ==> 0 <= stk[k] < nums2.Length
    {
      var idx := stk[top-1];
      if nums2[idx] < nums2[i] {
        top := top - 1;
        m := m[nums2[idx] := nums2[i]];
      } else {
        break;
      }
    }
    assert top < nums2.Length;
    stk[top] := i;
    top := top + 1;
    i := i + 1;
  }
  while top > 0
    decreases top
    invariant 0 <= top <= nums2.Length
    invariant forall k :: 0 <= k < top ==> 0 <= stk[k] < nums2.Length
  {
    top := top - 1;
    var idx := stk[top];
    m := m[nums2[idx] := -1];
  }
  var j := 0;
  while j < nums1.Length
    decreases nums1.Length - j
    invariant 0 <= j <= nums1.Length
    invariant result.Length == nums1.Length
  {
    var v := if nums1[j] in m then m[nums1[j]] else -1;
    result[j] := v;
    j := j + 1;
  }
}
// </vc-code>
