// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type declaration for `v` from `array<int>` to `seq<int>` in the helper function signature and implementation to resolve compilation errors. */
function CountElementsLessOrEqual(v: seq<int>, e: int): int
{
  (if v.Length == 0 then 0 else (if v[0] <= e then 1 else 0) + CountElementsLessOrEqual(v[1..], e))
}
// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)
    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && (exists j :: 0 <= j < v.Length && v[j] == result[k])
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> (exists j :: 0 <= j < result.Length && result[j] == v[k])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected the type casting for the invariant in the loop. It now correctly uses `v[0..i]`, which is already a sequence, resolving the compilation error. */
{
    var count_le := 0;
    if v.Length > 0 {
      for i := 0 to v.Length - 1
        invariant 0 <= i <= v.Length
        invariant history i: forall k :: 0 <= k < i ==> CountElementsLessOrEqual(v[0 .. i], e) ==
                                                CountElementsLessOrEqual(v[0 .. k], e) + (if v[k] <= e then 1 else 0)
        invariant count_le == CountElementsLessOrEqual(v[0 .. i], e)
      {
          if v[i] <= e
          {
              count_le := count_le + 1;
          }
      }
    }

    result := new int[count_le];
    var resultIndex := 0;
    if v.Length > 0 {
      for i := 0 to v.Length - 1
        invariant 0 <= i <= v.Length
        invariant 0 <= resultIndex <= count_le
        invariant forall k :: 0 <= k < resultIndex ==> result[k] <= e && (exists j :: 0 <= j < v.Length && v[j] == result[k])
        invariant forall k :: 0 <= k < resultIndex ==> (exists l :: 0 <= l < i && v[l] == result[k])
        invariant resultIndex == CountElementsLessOrEqual(v[0 .. i], e)
      {
          if v[i] <= e
          {
              result[resultIndex] := v[i];
              resultIndex := resultIndex + 1;
          }
      }
    }
}
// </vc-code>
