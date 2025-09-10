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
// </vc-helpers>

// <vc-spec>
method solve(N: int, H: int, A: seq<int>, B: seq<int>) returns (result: int)
  requires ValidInput(N, H, A, B)
  ensures result > 0
// </vc-spec>
// <vc-code>
{
    var maxA := maxSeq(A);
    var B_sorted := B;
    B_sorted := B_sorted సినిDescendingOrder();

    var currentDamage := 0;
    var hits := 0;

    for i := 0 to N - 1
        invariant 0 <= i <= N
        invariant currentDamage >= 0
        invariant hits >= 0
        invariant (forall j :: i <= j < N ==> B_sorted[j] <= B_sorted[i-1]) // B_sorted remains sorted desc
        invariant (forall j :: 0 <= j < i ==> B_sorted[j] >= B_sorted[i-1]) // Elements processed so far
        invariant (forall j :: 0 <= j < i ==> B_sorted[j] >= maxA || B_sorted[j] >= B_sorted[i])
        invariant currentDamage == sumSeq(B_sorted[0..i])
        invariant (forall j :: 0 <= j < i ==> B_sorted[j] >= maxA ==> B_sorted[j] == old(B_sorted[j])) // B_sorted elements are original
        invariant (forall j :: 0 <= j < i ==> B_sorted[j] < maxA ==> B_sorted[j] == old(B_sorted[j]))
    {
        if currentDamage >= H then
        {
            break;
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
    }

    return hits;
}

function ಸಿನಿDescendingOrder(s: seq<int>): seq<int>
  ensures |s| == | ಸಿನಿDescendingOrder(s)|
  ensures forall i, j :: 0 <= i < j < | ಸಿನಿDescendingOrder(s)| ==>   ಸಿನಿDescendingOrder(s)[i] >=   ಸಿನಿDescendingOrder(s)[j]
  ensures multiset(s) == multiset( ಸಿನಿDescendingOrder(s))
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var less := [];
    var greater := [];
    var equal := [];
    for i := 0 to |s| - 1
      invariant 0 <= i <= |s|
      invariant forall x :: x in less ==> x <= pivot
      invariant forall x :: x in greater ==> x > pivot
      invariant forall x :: x in equal ==> x == pivot
      invariant multiset(less) + multiset(greater) + multiset(equal) == multiset(s[0..i])
    {
      if s[i] < pivot then less := less + [s[i]];
      else if s[i] > pivot then greater := greater + [s[i]];
      else equal := equal + [s[i]];
    }
    ( ಸಿನಿDescendingOrder(greater) + equal +   ಸಿನಿDescendingOrder(less))
}
// </vc-code>

