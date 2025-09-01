

// <vc-helpers>
function IsSortedEven(s: seq<int>): bool
{
  forall i, j | 0 <= i < j && 2 * i < |s| && 2 * j < |s| :: s[2 * i] <= s[2 * j]
}

predicate IsEvenIndex(k: int)
{
    k % 2 == 0
}

predicate IsOddIndex(k: int)
{
    k % 2 == 1
}

ghost method SortInner(s: seq<int>) returns (sorted_s: seq<int>)
  ensures |sorted_s| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted_s| ==> sorted_s[i] <= sorted_s[j]
  ensures multiset(s) == multiset(sorted_s)
{
  if |s| <= 1 then
    return s;
  else
    var pivot := s[0];
    var smaller := SortInner(seq i | 0 < i < |s| && s[i] <= pivot :: s[i]);
    var larger := SortInner(seq i | 0 < i < |s| && s[i] > pivot :: s[i]);
    return smaller + [pivot] + larger;
}
// </vc-helpers>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var even_indices_count := (|a| - 1) / 2 + 1;
    var even_values_vec: seq<int> := seq(even_indices_count, i => a[2 * i]);
    var sorted_even_values_vec := SortInner(even_values_vec);

    var result := a;
    var even_idx := 0;
    for k := 0 to |a|
        invariant 0 <= k <= |a|
        invariant even_idx <= even_indices_count
        invariant forall i | 0 <= i < k && IsOddIndex(i) :: result[i] == a[i]
        invariant forall i | 0 <= i < k && IsEvenIndex(i) :: result[i] == sorted_even_values_vec[i / 2]
        invariant multiset(result[0..k] + a[k..|a|]) == multiset(a)
    {
        if k < |a| {
            if IsEvenIndex(k)
            {
                result := result[k := sorted_even_values_vec[even_idx]];
                even_idx := even_idx + 1;
            }
        }
    }
    return result;
}
// </vc-code>

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
{
  assume{:axiom} false;
}