predicate ValidInput(N: int, H: int, A: seq<int>, B: seq<int>)
{
    |A| == N && |B| == N && N > 0 && H > 0 &&
    (forall i :: 0 <= i < N ==> A[i] > 0 && B[i] > 0) &&
    (forall i :: 0 <= i < N ==> A[i] <= B[i])
}

function sumSeq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sumSeq(s[1..])
}

predicate MaxWieldExists(A: seq<int>, maxA: int)
{
    maxA in A && (forall i :: 0 <= i < |A| ==> A[i] <= maxA)
}

// <vc-helpers>
function maxSeq(s: seq<int>): int
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && s[i] == maxSeq(s)
  ensures forall i :: 0 <= i < |s| ==> s[i] <= maxSeq(s)
{
  if |s| == 1 then s[0]
  else
    var m_rest := maxSeq(s[1..]);
    if s[0] > m_rest then s[0] else m_rest
}

predicate SortedDescending(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
}

function SortDescending(s: seq<int>): seq<int>
  ensures |s| == |SortDescending(s)|
  ensures SortedDescending(SortDescending(s))
  ensures multiset(s) == multiset(SortDescending(s))
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var less: seq<int> := [];
    var greater: seq<int> := [];
    var equal: seq<int> := [];
    for i := 0 to |s|-1
      invariant 0 <= i <= |s|
      invariant multiset(s[..i]) == multiset(less) + multiset(greater) + multiset(equal)
      invariant forall x :: x in less ==> x < pivot
      invariant forall x :: x in greater ==> x > pivot
      invariant forall x :: x in equal ==> x == pivot
    {
      if s[i] < pivot then less := less + [s[i]];
      else if s[i] > pivot then greater := greater + [s[i]];
      else equal := equal + [s[i]];
    }
    (SortDescending(greater) + equal + SortDescending(less))
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, H: int, A: seq<int>, B: seq<int>) returns (result: int)
  requires ValidInput(N, H, A, B)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
    var maxA := maxSeq(A);
    var B_sorted := SortDescending(B);

    var currentDamage := 0;
    var hits := 0;

    for i := 0 to N
        invariant 0 <= i <= N
        invariant currentDamage >= 0
        invariant hits >= 0
        invariant SortedDescending(B_sorted)
        invariant multiset(B) == multiset(B_sorted)
        invariant (i == 0 || currentDamage == sumSeq(B_sorted[0..hits]))
        invariant (forall j :: 0 <= j < i ==> B_sorted[j] >= maxA || currentDamage >= H)
    {
        if currentDamage >= H then
        {
            break;
        }
        if i == N then
        {
          break; // All B_sorted values processed
        }

        if B_sorted[i] >= maxA
        {
            currentDamage := currentDamage + B_sorted[i];
            hits := hits + 1;
        } else
        {
            break; // No more attacks with B_sorted[i] will be effective enough
        }
    }

    if currentDamage < H
    {
        var remainingHealth := H - currentDamage;
        hits := hits + (remainingHealth + maxA - 1) / maxA;
        ghost assert remainingHealth > 0;
        ghost assert maxA > 0;
        assert (remainingHealth + maxA - 1) / maxA >= 1; // Since remainingHealth > 0 and maxA > 0
    }

    return hits;
}
// </vc-code>

