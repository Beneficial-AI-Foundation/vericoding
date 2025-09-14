

// <vc-helpers>
lemma LeNeqImpliesLt(a: int, b: int)
  requires a <= b
  requires a != b
  ensures a < b
{
}
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(nums: array<int>) returns (num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
// </vc-spec>
// <vc-code>
{
  var n := nums.Length;
  ghost var oldSeq: seq<int> := nums[..];
  var w := 0;
  var i := 0;
  assert forall a,b | 0 <= a && a < b && b < n :: oldSeq[a] <= oldSeq[b];
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= w <= i
    invariant forall a,b | 0 <= a && a < b && b < w :: nums[a] < nums[b]
    invariant forall k | 0 <= k < w :: exists j :: 0 <= j < i && nums[k] == oldSeq[j]
    invariant forall j | 0 <= j < i :: exists k :: 0 <= k < w && nums[k] == oldSeq[j]
    invariant forall k | i <= k < n :: nums[k] == oldSeq[k]
  {
    var v := nums[i];
    if w == 0 || v != nums[w-1] {
      if w != 0 {
        var j_idx :| 0 <= j_idx < i && nums[w-1] == oldSeq[j_idx];
        assert oldSeq[j_idx] <= oldSeq[i];
        assert oldSeq[j_idx] != oldSeq[i];
        calc {
          oldSeq[j_idx];
          <= oldSeq[i];
          <  oldSeq[i];
        }
        // Use lemma to convince Dafny (from <= and != derive <)
        LeNeqImpliesLt(oldSeq[j_idx], oldSeq[i]);
        assert oldSeq[j_idx] < oldSeq[i];
      }
      nums[w] := v;
      // After writing nums[w] := oldSeq[i], the element nums[w] corresponds to oldSeq[i]
      // This will be used after i is incremented to satisfy the invariants.
      w := w + 1;
    }
    i := i + 1;
  }
  return w;
}
// </vc-code>

