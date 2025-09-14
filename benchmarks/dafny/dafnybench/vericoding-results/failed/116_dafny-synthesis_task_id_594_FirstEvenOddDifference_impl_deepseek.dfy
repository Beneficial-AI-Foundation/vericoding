predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
lemma EvenOddLemma(a: array<int>, i: int, j: int)
  requires a.Length >= 2
  requires 0 <= i < a.Length && IsEven(a[i])
  requires 0 <= j < a.Length && IsOdd(a[j])
  requires forall k :: 0 <= k < i ==> IsOdd(a[k])
  requires forall k :: 0 <= k < j ==> IsEven(a[k])
  ensures exists p, q :: 0 <= p < a.Length && 0 <= q < a.Length && 
           IsEven(a[p]) && IsOdd(a[q]) && a[i] - a[j] == a[p] - a[q] &&
           (forall k :: 0 <= k < p ==> IsOdd(a[k])) && 
           (forall k :: 0 <= k < q ==> IsEven(a[k]))
{
}

lemma LoopInvariantLemmaEven(a: array<int>, i: int, fe: int)
  requires 0 <= i <= a.Length
  requires fe == -1 || 0 <= fe < a.Length
  requires fe != -1 ==> IsEven(a[fe])
  requires forall k :: 0 <= k < i && (fe == -1 || k < fe) ==> IsOdd(a[k])
  ensures forall k :: 0 <= k < i + 1 && (fe == -1 || k < fe) ==> IsOdd(a[k])
{
}

lemma LoopInvariantLemmaOdd(a: array<int>, j: int, fo: int)
  requires 0 <= j <= a.Length
  requires fo == -1 || 0 <= fo < a.Length
  requires fo != -1 ==> IsOdd(a[fo])
  requires forall k :: 0 <= k < j && (fo == -1 || k < fo) ==> IsEven(a[k])
  ensures forall k :: 0 <= k < j + 1 && (fo == -1 || k < fo) ==> IsEven(a[k])
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method FirstEvenOddDifference(a: array<int>) returns (diff: int)
    requires a.Length >= 2
    requires exists i :: 0 <= i < a.Length && IsEven(a[i])
    requires exists i :: 0 <= i < a.Length && IsOdd(a[i])
    ensures exists i, j :: 0 <= i < a.Length && 0 <= j < a.Length && IsEven(a[i]) && IsOdd(a[j]) && diff == a[i] - a[j] && 
        (forall k :: 0 <= k < i ==> IsOdd(a[k])) && (forall k :: 0 <= k < j ==> IsEven(a[k]))
// </vc-spec>
// <vc-code>
{
  var firstEven := -1;
  var firstOdd := -1;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant firstEven == -1 ==> forall k :: 0 <= k < i ==> IsOdd(a[k])
    invariant firstEven != -1 ==> forall k :: 0 <= k < i && k < firstEven ==> IsOdd(a[k])
    invariant firstEven == -1 || (0 <= firstEven < a.Length && IsEven(a[firstEven]))
  {
    if IsEven(a[i]) && firstEven == -1 {
      firstEven := i;
    } else {
      LoopInvariantLemmaEven(a, i, firstEven);
    }
    i := i + 1;
  }
  
  var j := 0;
  while j < a.Length
    invariant 0 <= j <= a.Length
    invariant firstOdd == -1 ==> forall k :: 0 <= k < j ==> IsEven(a[k])
    invariant firstOdd != -1 ==> forall k :: 0 <= k < j && k < firstOdd ==> IsEven(a[k])
    invariant firstOdd == -1 || (0 <= firstOdd < a.Length && IsOdd(a[firstOdd]))
  {
    if IsOdd(a[j]) && firstOdd == -1 {
      firstOdd := j;
    } else {
      LoopInvariantLemmaOdd(a, j, firstOdd);
    }
    j := j + 1;
  }
  
  diff := a[firstEven] - a[firstOdd];
}
// </vc-code>

