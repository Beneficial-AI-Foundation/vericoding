// <vc-preamble>
predicate BinarySearchPrecond(a: array<int>, key: int)
    reads a
{
    forall i, j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}
method BinarySearchLoop(a: array<int>, key: int, lo: nat, hi: nat) returns (result: nat)
    requires lo <= hi
    requires hi <= a.Length
    requires BinarySearchPrecond(a, key)
    ensures lo <= result <= hi
    ensures forall i :: lo <= i < result ==> a[i] < key
    ensures forall i :: result <= i < hi ==> a[i] >= key
    decreases hi - lo
{
    if lo < hi {
        var mid := lo + (hi - lo) / 2;
        if a[mid] < key {
            result := BinarySearchLoop(a, key, mid + 1, hi);
        } else {
            result := BinarySearchLoop(a, key, lo, mid);
        }
    } else {
        result := lo;
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): recursive lemma proving properties of BinarySearchLoop without calling methods */
lemma BinarySearchLoopLemma(a: array<int>, key: int, lo: nat, hi: nat) returns (r: nat)
    requires lo <= hi
    requires hi <= a.Length
    requires BinarySearchPrecond(a, key)
    ensures lo <= r <= hi
    ensures forall i :: lo <= i < r ==> a[i] < key
    ensures forall i :: r <= i < hi ==> a[i] >= key
    decreases hi - lo
{
    if lo < hi {
        var mid := lo + (hi - lo) / 2;
        if a[mid] < key {
            var rr := BinarySearchLoopLemma(a, key, mid + 1, hi);
            r := rr;
        } else {
            var rr := BinarySearchLoopLemma(a, key, lo, mid);
            r := rr;
        }
    } else {
        r := lo;
    }
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, key: int) returns (result: nat)
    requires BinarySearchPrecond(a, key)
    ensures result <= a.Length
    ensures forall i :: 0 <= i < result ==> a[i] < key
    ensures forall i :: result <= i < a.Length ==> a[i] >= key
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): call BinarySearchLoop and return its result */
  result := BinarySearchLoop(a, key, 0, a.Length);
}

// </vc-code>
